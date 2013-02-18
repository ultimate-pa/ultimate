package local.stalin.plugins.generator.rcfgbuilder;

public class ProgramPoint {

	final private String procedure;
	final private String location;
	final private boolean isErrorLocation;
	
	
	public ProgramPoint(String procedure, String location,
													boolean isErrorLocation) {
		this.procedure = procedure;
		this.location = location;
		this.isErrorLocation = isErrorLocation;
	}
	/**
	 * @return the procedure
	 */
	public String getProcedure() {
		return procedure;
	}
	/**
	 * @return the location
	 */
	public String getLocation() {
		return location;
	}
	
	public boolean isErrorLocation() {
		return isErrorLocation;
	}

	
	
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof ProgramPoint) {
			ProgramPoint pp2 = (ProgramPoint) obj;
			return this.procedure.equals(pp2.getProcedure()) &&
				this.location.equals(pp2.getLocation());
		}
		else {
			return false;
		}
	}

	
	@Override
	public int hashCode() {
		return 3 * this.location.hashCode() + 5 * this.procedure.hashCode();
	}

	@Override
	public String toString() {
		return "_Proc:" + procedure + "_Loc:" + location + "_";
	}
	
	
	
}
