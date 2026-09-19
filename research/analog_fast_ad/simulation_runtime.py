"""Host execution budgets only; never alter the electrical model or accuracy tests."""
import os

def positive_integer(name, default):
    value = int(os.environ.get(name, default))
    if value <= 0:
        raise ValueError(f"{name} must be a positive integer")
    return value

def spice_timeout():
    return positive_integer("PANDROSION_SPICE_TIMEOUT_SECONDS", 90)

def campaign_workers():
    return positive_integer("PANDROSION_SPICE_WORKERS", 3)
