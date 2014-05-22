package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

public class DummyCodeBlock extends CodeBlock {

	private static final long serialVersionUID = 1L;

	public DummyCodeBlock() {
		super(null, null);
		// TODO Auto-generated constructor stub
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] {};
	}

	@Override
	public String getPrettyPrintedStatements() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public String toString() {
		return "DUMMYCODEBLOCK";
	}

}
