package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
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
					|| codeBlocks[i] instanceof ParallelComposition
					|| codeBlocks[i] instanceof Call
					|| codeBlocks[i] instanceof Return
					|| codeBlocks[i] instanceof Summary)) {
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
				m_TransitionFormula = TransFormula.sequentialComposition(this.getSerialNumer(),boogie2smt,
						m_TransitionFormula, 
						codeBlocks[i].getTransitionFormula()
						);
				m_TransitionFormulaWithBranchEncoders = TransFormula.sequentialComposition(this.getSerialNumer(),boogie2smt,
						m_TransitionFormulaWithBranchEncoders, 
						codeBlocks[i].getTransitionFormulaWithBranchEncoders());
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
	
	
	
	/**
	 * Returns Transformula for a sequence of CodeBlocks that may (opposed to 
	 * the method sequentialComposition) contain also Call and Return.
	 */
	public static TransFormula getInterproceduralTransFormula(
			Boogie2SMT boogie2smt, CodeBlock... codeBlocks) {
		return getInterproceduralTransFormula(boogie2smt, null, null, codeBlocks);
	}
	
	
	private static TransFormula getInterproceduralTransFormula(
			Boogie2SMT boogie2smt, Call call, Return ret, CodeBlock... codeBlocks) {
		List<TransFormula> localTransFormulas = new ArrayList<TransFormula>();
		Call firstCall = null;
		int seenCalls = 0;
		int seenReturns = 0;
		List<CodeBlock> afterFirstCall = new ArrayList<CodeBlock>();
		for (int i = 0; i < codeBlocks.length; i++) {
			if (firstCall == null) {
				if (codeBlocks[i] instanceof Call) {
					firstCall = (Call) codeBlocks[i];
					seenCalls++;
				} else {
					assert !(codeBlocks[i] instanceof Return);
					localTransFormulas.add(codeBlocks[i].getTransitionFormula());
				}
			} else {
				if (codeBlocks[i] instanceof Return) {
					seenReturns++;
					if (seenCalls == seenReturns) {
						Return correspondingReturn = (Return) codeBlocks[i];
						CodeBlock[] codeBlocksBetween = 
								afterFirstCall.toArray(new CodeBlock[0]); 
						TransFormula localTransFormula = getInterproceduralTransFormula(
								boogie2smt,	firstCall, correspondingReturn, codeBlocksBetween);
						localTransFormulas.add(localTransFormula);
						firstCall = null;
						seenCalls = 0;
						seenReturns = 0;
					}
					assert (seenCalls >= seenReturns);
				} else if (codeBlocks[i] instanceof Call) {
					seenCalls++;
					afterFirstCall.add(codeBlocks[i]);
				} else {
					afterFirstCall.add(codeBlocks[i]);
				}
			}
		}
		if (firstCall != null) {
			CodeBlock[] codeBlocksBetween = afterFirstCall.toArray(new CodeBlock[0]); 
			TransFormula localTransFormula = getInterproceduralTransFormula(
					boogie2smt, firstCall, null, codeBlocksBetween);
			localTransFormulas.add(localTransFormula);
		}
		TransFormula localTransFormula = TransFormula.sequentialComposition(
				20000, boogie2smt, localTransFormulas.toArray(new TransFormula[0]));
		if (call == null) {
			return localTransFormula;
		} else {
			TransFormula callTf = call.getTransitionFormula();
			Set<BoogieVar> inParams = callTf.getOutVars().keySet();
			Set<BoogieVar> outParams;
			if (ret == null) {
				outParams = new HashSet<BoogieVar>(0);
			} else {
				outParams = ret.getTransitionFormula().getInVars().keySet();
			}
			TransFormula summaryTf = TransFormula.procedureSummary(
					boogie2smt, localTransFormula, inParams, outParams);
			if (ret == null) {
				return TransFormula.sequentialComposition(40000, boogie2smt, callTf, summaryTf);
			} else {
				return TransFormula.sequentialComposition(40000, boogie2smt, callTf, summaryTf, ret.getTransitionFormula());
			}
		}
	}
	
}
