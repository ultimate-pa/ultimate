package pea.reqCheck;

import pea.Phase;


//mapt eine Phase in einem pea auf den h�chsten index der phase
//zum index: da wir auch states wie stinit haben, werden diese auf 0 gemapt, alle anderen states werden um daher um eine
//zahl nach oben gesetzt: stinit-->0, st0-->1; st0123-->4
public class PEAPhaseIndexMap {
	
	private Phase phase;
	private String name;
	private int index;
	private boolean wait; //true iff phase is in wait, false else
	
	
	public PEAPhaseIndexMap(Phase phase){
		wait = false;
		setPhase(phase);
		final String name = phase.getName();
		final int nameLength = name.length();
		if (nameLength < 1){
			setIndex(0);
			setPhase(phase);
		}
		else
		{
		char c = name.charAt(nameLength-1);
		if(c=='W'){ //for states with clockInvariants the stateName has a "W" or "X" at the end; however we are only interested in the phaseNr
			c = name.charAt(nameLength-2);
			wait = true; //bei W m�ssen wir die Phase davor (TimeBound noch nicht vollst�ndig gelesen) von der danach unterscheiden
			}
			else if (c=='X'){
				c = name.charAt(nameLength-2);
		}
		try {
			int value = Integer.parseInt(name.valueOf(c));
			value = (value+1) *2;
			if (wait==true){
				value = value - 1;
			}
			setIndex(value);
		} catch (final NumberFormatException e) {
			setIndex(0);
		}		
		
	}}
	
	public PEAPhaseIndexMap(String name){
		setName(name);
		wait = false;
		final int nameLength = name.length();
		if (nameLength < 1){
			setIndex(0);
		}
		else
		{
		char c = name.charAt(nameLength-1);
		if (c=='W'|| c=='X')//in dem Fall ist per Konstruktion der Name l�nger 2
		{
			c = name.charAt(nameLength-2);
		}
		if (c=='W')//in dem Fall ist per Konstruktion der Name l�nger 2
		{
			wait = true;
		}
		try {
			int value = Integer.parseInt(name.valueOf(c));
			value = (value +1)*2;
			if (wait = true){
				value = value +1;
			}
			setIndex(value);
		} catch (final NumberFormatException e) {
			setIndex(0);
		}		
		
	}}
	
	
	private void setPhase(Phase phase) {
		this.phase = phase;
	}
	public Phase getPhase() {
		return phase;
	}
	private void setIndex(int d) {
		index = d;
	}
	public int getIndex() {
		return index;
	}
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}
	
	
	
}
