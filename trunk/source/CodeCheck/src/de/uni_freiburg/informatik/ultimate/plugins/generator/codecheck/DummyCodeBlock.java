package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

public class DummyCodeBlock extends CodeBlock {

	public DummyCodeBlock(ProgramPoint source, ProgramPoint target) {
		super(source, target);
		// TODO Auto-generated constructor stub
	}
	
	public DummyCodeBlock() {
		super(null, null);
		// TODO Auto-generated constructor stub
	}

	@Override
	protected String[] getFieldNames() {
		// TODO Auto-generated method stub
		return null;
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

}
