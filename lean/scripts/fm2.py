"""Read FM2 frame rows as (command, controller 1, controller 2) and read the
romChecksum header. Controller bytes use bit 7 for Right through bit 0 for A.
The proof input convention drops the first idle row and permits no later commands."""
import base64, hashlib


def pad(field):
    """A controller field, as emu/movie.h accepts it: exactly 8 characters, each '.' or ' ' or the
    button's letter in the order RLDUTSBA."""
    assert len(field) == 8 and all(c in ". " + e for c, e in zip(field, "RLDUTSBA")), field
    return sum(1 << (7 - j) for j, c in enumerate(field) if c not in ". ")


def load(path):
    """Returns (frames, checksum); frames is a list of (cmd, p1, p2)."""
    text = open(path, encoding="latin-1").read()
    checksum, frames = "", []
    for line in text.splitlines():
        if line.startswith("romChecksum "):
            checksum = line.split(" ", 1)[1].strip()
        elif line.startswith("|"):
            parts = line.split("|")
            assert len(parts) >= 4 and parts[1].isdigit(), (len(frames), line)
            cmd = int(parts[1])
            assert cmd & ~3 == 0, (len(frames), cmd)
            p2 = pad(parts[3]) if parts[3] else 0
            frames.append((cmd, pad(parts[2]), p2))
    assert frames, "no frames"
    return frames, checksum


def rom_checksum(rom_path):
    """The movie header's romChecksum for an iNES file: base64 of MD5(PRG+CHR)."""
    return "base64:" + base64.b64encode(hashlib.md5(open(rom_path, "rb").read()[16:]).digest()).decode()
