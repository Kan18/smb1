"""Finite byte checks for Mario's Y mover and collision entry windows."""


def signed8(value):
    return value if value < 128 else value - 256


def velocity(speed, force):
    return signed8(speed) * 256 + force


def y_step(high, pixel, dummy, speed, force):
    old = ((high << 8) | pixel) * 256 + dummy
    carry = (dummy + force) >> 8
    new_dummy = (dummy + force) & 255
    new_pixel = (pixel + signed8(speed) + carry) & 255
    page_delta = (pixel + signed8(speed) + carry) // 256
    new_high = (high + page_delta) & 255
    new = ((new_high << 8) | new_pixel) * 256 + new_dummy
    delta = (new - old) & 0xFFFFFF
    if delta >= 0x800000:
        delta -= 0x1000000
    return delta, new_high, new_pixel, new_dummy


def gravity(speed, force, down, maximum=4):
    added = force + down
    new_force = added & 255
    new_speed = (speed + (added >> 8)) & 255
    # The ROM uses the sign bit of CMP, not a signed comparison.
    if ((new_speed - maximum) & 128) == 0 and new_force >= 128:
        return maximum, 0
    return new_speed, new_force


def within_max(speed, force, maximum=4):
    return signed8(speed) < maximum or (speed == maximum and force < 128)


def head_changes_row(offset, old_y, new_y):
    return ((old_y + offset) & 255) >> 4 != ((new_y + offset) & 255) >> 4


def main():
    checked = 0
    for speed in range(256):
        for force in range(256):
            for dummy in (0, 0x7F, 0xFE, 0xFF):
                for high, pixel in ((1, 0x2F), (1, 0xFF), (0, 0xFF)):
                    delta, *_ = y_step(high, pixel, dummy, speed, force)
                    assert delta == velocity(speed, force)
                    checked += 1
    max_fall = 0
    for speed in list(range(0, 5)) + list(range(192, 256)):
        for force in range(256):
            if not within_max(speed, force):
                continue
            for down in range(0x91):
                new_speed, new_force = gravity(speed, force, down)
                new_velocity = (new_speed << 8) | new_force
                if new_speed < 128:
                    max_fall = max(max_fall, new_velocity)
                    assert new_velocity <= 0x050F
    assert max_fall == 0x050F
    assert gravity(0x80, 0x80, 0x50) == (4, 0)

    # Over-approximate any three ordinary descent updates after a coin.
    # Gravity may vary arbitrarily from 0 through $90 on each update;
    # actual jump classes keep their falling force fixed, so this is generous.
    initial = []
    for signed_speed in range(-5, 6):
        for force in range(256):
            if signed_speed == 5 and force > 0x0F:
                continue
            initial.append(((signed_speed & 255) << 8) | force)
    progress = {v: 0 for v in initial}
    for _ in range(3):
        next_progress = {}
        for v, amount in progress.items():
            signed_v = v if v < 0x8000 else v - 0x10000
            for down in range(0x91):
                new_speed, new_force = gravity(v >> 8, v & 255, down)
                new_v = (new_speed << 8) | new_force
                next_progress[new_v] = max(
                    next_progress.get(new_v, -1_000_000), amount + signed_v
                )
        progress = next_progress
    max_three_down = max(progress.values())
    assert max_three_down == 4253
    # A target head check at Y >= $6c00 after even the weakest ordinary
    # stomp rise ($fdff = -$0201) needs pre-rise Y >= $6e01.
    needed_from_last_coin = 0x6E01 - 0x5BFF
    assert needed_from_last_coin == 4610
    assert max_three_down < needed_from_last_coin

    # Jump start zeros the position fraction before the first -5 px move.
    jump_steps = [velocity(0xFB, 0) - old_dummy for old_dummy in range(256)]
    assert min(jump_steps) == -1535 and max(jump_steps) == -1280

    for old_y in range(0x40, 0xE1):
        for step in range(1, 9):
            new_y = old_y - step
            if head_changes_row(4, old_y, new_y):
                assert (new_y & 15) >= 4
        for step in range(1, 11):
            new_y = old_y - step
            for offset in (2, 0x12):
                if head_changes_row(offset, old_y, new_y):
                    assert (new_y & 15) >= 4
    assert head_changes_row(4, 0x6C, 0x63) and (0x63 & 15) < 4

    old = 0x01AFFE
    moved = (old + 0x050F) & 0xFFFFFF
    assert moved == 0x01B50D and ((moved >> 8) & 15) == 5
    print(f"Y position byte cases checked: {checked}")
    print(f"withinMax speed/fraction shape: fall velocity after gravity <= ${max_fall:04x}")
    print("fresh -5 jump with fraction reset: -1280..-1535/256 px")
    print("head row entry: rise <=8 big or <=10 small/swim cannot skip Y low 4")
    print("floor skip state: $01affe + $050f = $01b50d, first entry low nibble 5")
    print(f"three arbitrary-gravity descent updates: max {max_three_down}/256 px < {needed_from_last_coin}/256 px needed before weakest ordinary stomp rise")
    print("exceptional speed $80/$80 + gravity $50 clamps to $0400")


if __name__ == "__main__":
    main()
