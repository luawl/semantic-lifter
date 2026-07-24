const std = @import("std");

const Ed25519 = std.crypto.sign.Ed25519;
const Sha256 = std.crypto.hash.sha2.Sha256;
const Dir = std.Io.Dir;
const File = std.Io.File;

const domain = "lifter-target-proof-bundle-attestation-v1\x00";
const max_bundle_bytes = 1024 * 1024;

fn decodeHex(comptime byte_length: usize, text: []const u8) ![byte_length]u8 {
    if (text.len != byte_length * 2) return error.InvalidHexLength;
    var bytes: [byte_length]u8 = undefined;
    _ = try std.fmt.hexToBytes(&bytes, text);
    return bytes;
}

fn verifyBytes(message: []const u8, signature_bytes: [Ed25519.Signature.encoded_length]u8, public_key_bytes: [Ed25519.PublicKey.encoded_length]u8) !void {
    const signature = Ed25519.Signature.fromBytes(signature_bytes);
    const public_key = try Ed25519.PublicKey.fromBytes(public_key_bytes);
    var verifier = try signature.verifier(public_key);
    verifier.update(domain);
    verifier.update(message);
    try verifier.verifyStrict();
}

fn verifyDigest(message: []const u8, expected: [Sha256.digest_length]u8) !void {
    var actual: [Sha256.digest_length]u8 = undefined;
    Sha256.hash(message, &actual, .{});
    if (!std.mem.eql(u8, &actual, &expected)) return error.BundleDigestMismatch;
}

fn signAlloc(allocator: std.mem.Allocator, message: []const u8, seed: [Ed25519.KeyPair.seed_length]u8) !struct {
    public_key: [Ed25519.PublicKey.encoded_length]u8,
    signature: [Ed25519.Signature.encoded_length]u8,
} {
    const key_pair = try Ed25519.KeyPair.generateDeterministic(seed);
    const signed_message = try std.mem.concat(allocator, u8, &.{ domain, message });
    defer allocator.free(signed_message);
    const signature = try key_pair.sign(signed_message, null);
    return .{
        .public_key = key_pair.public_key.toBytes(),
        .signature = signature.toBytes(),
    };
}

fn usage() void {
    std.debug.print(
        \\usage:
        \\  proof-attest verify <signature-hex> <trusted-public-key-hex>
        \\  proof-attest verify-file <bundle-path> <bundle-sha256> <signature-hex> <trusted-public-key-hex>
        \\The verify command reads exact bundle bytes from stdin.
        \\The verify-file command requires the expected digest of the supplied file.
        \\
    , .{});
}

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const allocator = init.gpa;
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len < 2) {
        usage();
        return error.MissingCommand;
    }

    if (std.mem.eql(u8, args[1], "verify")) {
        if (args.len != 4) {
            usage();
            return error.InvalidArguments;
        }
        var stdin_buffer: [8192]u8 = undefined;
        var stdin_reader = File.stdin().readerStreaming(io, &stdin_buffer);
        const message = try stdin_reader.interface.allocRemaining(allocator, .limited(max_bundle_bytes));
        defer allocator.free(message);
        if (message.len == 0) return error.EmptyBundle;
        try verifyBytes(
            message,
            try decodeHex(Ed25519.Signature.encoded_length, args[2]),
            try decodeHex(Ed25519.PublicKey.encoded_length, args[3]),
        );
        return;
    }

    if (std.mem.eql(u8, args[1], "verify-file")) {
        if (args.len != 6) {
            usage();
            return error.InvalidArguments;
        }
        const message = try Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_bundle_bytes));
        defer allocator.free(message);
        if (message.len == 0) return error.EmptyBundle;
        try verifyDigest(message, try decodeHex(Sha256.digest_length, args[3]));
        try verifyBytes(
            message,
            try decodeHex(Ed25519.Signature.encoded_length, args[4]),
            try decodeHex(Ed25519.PublicKey.encoded_length, args[5]),
        );
        return;
    }

    usage();
    return error.UnknownCommand;
}

test "detached proof attestation binds exact bytes and trusted key" {
    const seed = [_]u8{0x42} ** Ed25519.KeyPair.seed_length;
    const message = "one bounded proof bundle";
    const attestation = try signAlloc(std.testing.allocator, message, seed);
    var digest: [Sha256.digest_length]u8 = undefined;
    Sha256.hash(message, &digest, .{});
    try verifyDigest(message, digest);
    digest[0] ^= 1;
    try std.testing.expectError(error.BundleDigestMismatch, verifyDigest(message, digest));
    try verifyBytes(message, attestation.signature, attestation.public_key);
    try std.testing.expectError(
        error.SignatureVerificationFailed,
        verifyBytes("one tampered proof bundle", attestation.signature, attestation.public_key),
    );

    const other = try signAlloc(std.testing.allocator, message, [_]u8{0x24} ** Ed25519.KeyPair.seed_length);
    try std.testing.expectError(
        error.SignatureVerificationFailed,
        verifyBytes(message, attestation.signature, other.public_key),
    );
}
