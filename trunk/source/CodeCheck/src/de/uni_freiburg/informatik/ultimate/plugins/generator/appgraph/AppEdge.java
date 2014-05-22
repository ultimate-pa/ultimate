package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class AppEdge extends
		ModifiableMultigraphEdge<AnnotatedProgramPoint, AppEdge> {

	private static final long serialVersionUID = 1L;
	
	CodeBlock statement;

	public AppEdge(AnnotatedProgramPoint source, CodeBlock statement, AnnotatedProgramPoint target) {
		super(source, target);
		assert source != null && target != null && statement != null;
		this.statement = statement;
	}
	
	public CodeBlock getStatement() {
		return statement;
	}

	public void disconnect() {
		boolean success = true;
		success &= this.mSource.removeOutgoing(this);
		success &= this.mTarget.removeIncoming(this);
		assert success;
		this.mSource = null;
		this.mTarget = null;
	}
	
	public String toString() {
		return String.format("%s -- %s --> %s", this.mSource, this.statement, this.mTarget);
	}
}
