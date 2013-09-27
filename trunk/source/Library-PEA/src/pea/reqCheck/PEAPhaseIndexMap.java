package pea.reqCheck;

import pea.Phase;


//mapt eine Phase in einem pea auf den höchsten index der phase
//zum index: da wir auch states wie stinit haben, werden diese auf 0 gemapt, alle anderen states werden um daher um eine
//zahl nach oben gesetzt: stinit-->0, st0-->1; st0123-->4
public class PEAPhaseIndexMap {
	
	private Phase phase;
	private String name;
	private int index;
	private boolean wait; //true iff phase is in wait, false else
	
	
	public PEAPhaseIndexMap(Phase phase){
		wait = false;
		this.setPhase(phase);
		String name = phase.getName();
		int nameLength = name.length();
		if (nameLength < 1){
			this.setIndex(0);
			this.setPhase(phase);
		}
		else
		{
		char c = name.charAt(nameLength-1);
		if(c=='W'){ //for states with clockInvariants the stateName has a "W" or "X" at the end; however we are only interested in the phaseNr
			c = name.charAt(nameLength-2);
			wait = true; //bei W müssen wir die Phase davor (TimeBound noch nicht vollständig gelesen) von der danach unterscheiden
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
			this.setIndex(value);
		} catch (NumberFormatException e) {
			this.setIndex(0);
		}		
		
	}}
	
	public PEAPhaseIndexMap(String name){
		setName(name);
		wait = false;
		int nameLength = name.length();
		if (nameLength < 1){
			this.setIndex(0);
		}
		else
		{
		char c = name.charAt(nameLength-1);
		if (c=='W'|| c=='X')//in dem Fall ist per Konstruktion der Name länger 2
		{
			c = name.charAt(nameLength-2);
		}
		if (c=='W')//in dem Fall ist per Konstruktion der Name länger 2
		{
			wait = true;
		}
		try {
			int value = Integer.parseInt(name.valueOf(c));
			value = (value +1)*2;
			if (wait = true){
				value = value +1;
			}
			this.setIndex(value);
		} catch (NumberFormatException e) {
			this.setIndex(0);
		}		
		
	}}
	
	
	private void setPhase(Phase phase) {
		this.phase = phase;
	}
	public Phase getPhase() {
		return phase;
	}
	private void setIndex(int d) {
		this.index = d;
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
