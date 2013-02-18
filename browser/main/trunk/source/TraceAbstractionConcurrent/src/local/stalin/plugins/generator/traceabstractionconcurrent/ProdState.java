package local.stalin.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.List;

import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;

public class ProdState extends StateFormula implements IProgramState {

	/**
	 * 
	 */
	private static final long serialVersionUID = -8826942011742605334L;
	
	List<ProgramPoint> m_ProgramPoints = new ArrayList<ProgramPoint>();
	
	public ProdState(List<ProgramPoint> mProgramPoints) {
		super(null);
		m_ProgramPoints = mProgramPoints;
	}

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoints", "Formula", "Vars", "OldVars"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "ProgramPoints")
			return m_ProgramPoints;
		else 
			return super.getFieldValue(field);
	}

	public void addProgramPoint(ProgramPoint programPoint) {
		m_ProgramPoints.add(programPoint);
	}
	
	public List<ProgramPoint> getProgramPoints() {
		return m_ProgramPoints;
	}

	/* (non-Javadoc)
	 * @see local.stalin.plugins.generator.rcfgbuilder.StateFormula#toString()
	 */
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		for (ProgramPoint pp : getProgramPoints())
			result.append(pp.getLocation()  + ",");
		return result.toString();
	}
	
	
}
