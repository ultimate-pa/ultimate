package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IRCFGVisitor;

/**
 * Represents an edge without any effect to the programs variables. While
 * constructing the CFG of a Boogie program these edges are used temporarily
 * but do not occur in the result.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class GotoEdge extends CodeBlock {

	private static final long serialVersionUID = -2923506946454722306L;

	GotoEdge(int serialNumber, ProgramPoint source, ProgramPoint target, Logger logger) {
		super(serialNumber, source, target, logger);
		assert (target != null);
	}

	@Override
	public void updatePayloadName() {
		getPayload().setName("goto");
	}

	@Override
	public String getPrettyPrintedStatements() {
		return "goto " + mTarget.toString();
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] {};
	}

	@Override
	public String toString() {
		return "goto;";
	}


	/**
     * Implementing the visitor pattern
     */
	@Override
	public void accept(IRCFGVisitor visitor) {
		visitor.visitEdge(this);
		visitor.visitCodeBlock(this);
		visitor.visit(this);
		visitor.visitedCodeBlock(this);
		visitor.visitedEdge(this);
	}
}
