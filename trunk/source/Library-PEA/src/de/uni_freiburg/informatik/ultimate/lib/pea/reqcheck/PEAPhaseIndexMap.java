package de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck;

import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;

//mapt eine Phase in einem pea auf den h�chsten index der phase
//zum index: da wir auch states wie stinit haben, werden diese auf 0 gemapt, alle anderen states werden um daher um eine
//zahl nach oben gesetzt: stinit-->0, st0-->1; st0123-->4
public class PEAPhaseIndexMap {
	
	private Phase phase;
	private String name;
	private int index;
	private boolean wait; //true iff phase is in wait, false else
	
	public PEAPhaseIndexMap(final Phase phase) {
		wait = false;
		setPhase(phase);
		final String name = phase.getName();
		final int nameLength = name.length();
		if (nameLength < 1) {
			setIndex(0);
			setPhase(phase);
		} else {
			char c = name.charAt(nameLength - 1);
			if (c == 'W') {
				// for states with clockInvariants the stateName has a "W" or "X" at the end; however we are only
				// interested in the phaseNr
				c = name.charAt(nameLength - 2);
				// with W we have to distinguish the phase (TimeBound not yet fully read) from the next one
				wait = true;
			} else if (c == 'X') {
				c = name.charAt(nameLength - 2);
			}
			try {
				int value = Integer.parseInt(String.valueOf(c));
				value = (value + 1) * 2;
				if (wait) {
					value = value - 1;
				}
				setIndex(value);
			} catch (final NumberFormatException e) {
				setIndex(0);
			}
		}
	}
	
	public PEAPhaseIndexMap(final String name) {
		setName(name);
		wait = false;
		final int nameLength = name.length();
		if (nameLength < 1) {
			setIndex(0);
		} else {
			char c = name.charAt(nameLength - 1);
			if (c == 'W' || c == 'X') {
				// the name length is greater than 2 by construction
				c = name.charAt(nameLength - 2);
			}
			if (c == 'W') {
				wait = true;
			}
			try {
				int value = Integer.parseInt(String.valueOf(c));
				value = (value + 1) * 2;
				if (wait) {
					value = value + 1;
				}
				setIndex(value);
			} catch (final NumberFormatException e) {
				setIndex(0);
			}
			
		}
	}
	
	private void setPhase(final Phase phase) {
		this.phase = phase;
	}
	
	public Phase getPhase() {
		return phase;
	}
	
	private void setIndex(final int d) {
		index = d;
	}
	
	public int getIndex() {
		return index;
	}
	
	public String getName() {
		return name;
	}
	
	public void setName(final String name) {
		this.name = name;
	}
}
