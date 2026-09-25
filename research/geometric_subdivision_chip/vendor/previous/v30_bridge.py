"""Portable import adapter; reference V30 modules are the repository originals."""
import sys
from pathlib import Path
V30=Path(__file__).resolve().parents[4]/'research/analog_fast_ad'
sys.path.insert(0,str(V30))
from model import prepare,schedule,decode
from joint_spice import config
from calibrate_cells import calibrate
from revised_circuit import calibrate_adc
from simulation_runtime import spice_timeout,campaign_workers
