package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;


/**
 * Edge in a recursive control flow graph that represents a sequence of 
 * CodeBlocks which are executed one after the other if this edge is 
 * executed.
 */
public class SequentialComposition extends CodeBlock {
	
	private static final long serialVersionUID = 9192152338120598669L;
	private final CodeBlock[] m_CodeBlocks;
	private final String m_PrettyPrinted;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"CodeBlocks (Sequentially Composed)", "PrettyPrintedStatements", "TransitionFormula",
		"OccurenceInCounterexamples"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "CodeBlocks (Sequentially Composed)") {
			return m_CodeBlocks;
		}
		else if (field == "PrettyPrintedStatements") {
			return m_PrettyPrinted;
		}
		else if (field == "TransitionFormula") {
			return m_TransitionFormula;
		}
		else if (field == "OccurenceInCounterexamples") {
			return m_OccurenceInCounterexamples;
		}
		else {
			throw new UnsupportedOperationException("Unknown field "+field);
		}
	}
	
	
	public SequentialComposition(ProgramPoint source, ProgramPoint target,
			Boogie2SMT boogie2smt,
			CodeBlock... codeBlocks) {
		super(source, target);
		this.m_CodeBlocks = codeBlocks;
		
		StringBuilder prettyPrinted = new StringBuilder();
		
		for (int i=0; i<codeBlocks.length; i++) {
			if (! (codeBlocks[i] instanceof StatementSequence 
					|| codeBlocks[i] instanceof SequentialComposition
					|| codeBlocks[i] instanceof ParallelComposition)) {
				throw new IllegalArgumentException("Only StatementSequence," +
						" SequentialComposition, and ParallelComposition supported");
			}
			codeBlocks[i].disconnectSource();
			codeBlocks[i].disconnectTarget();
			prettyPrinted.append(codeBlocks[i].getPrettyPrintedStatements());
			
			if (i==0) {
				m_TransitionFormula = codeBlocks[0].getTransitionFormula();
				m_TransitionFormulaWithBranchEncoders = 
						codeBlocks[0].getTransitionFormulaWithBranchEncoders();
			} else {
				m_TransitionFormula = TransFormula.sequentialComposition(
						m_TransitionFormula, 
						codeBlocks[i].getTransitionFormula(),
						boogie2smt, this.getSerialNumer());
				m_TransitionFormulaWithBranchEncoders = TransFormula.sequentialComposition(
						m_TransitionFormulaWithBranchEncoders, 
						codeBlocks[i].getTransitionFormulaWithBranchEncoders(),
						boogie2smt, this.getSerialNumer());
			}
		}
		m_PrettyPrinted = prettyPrinted.toString();
		updatePayloadName();
	}

	@Override
	public String getPrettyPrintedStatements() {
		return m_PrettyPrinted;
	}

	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		throw new UnsupportedOperationException();
	}

	public CodeBlock[] getCodeBlocks() {
		return m_CodeBlocks;
	}

	@Override
	public void setTransitionFormula(TransFormula transFormula) {
		throw new UnsupportedOperationException(
				"transition formula is computed in constructor");
	}
	
}
