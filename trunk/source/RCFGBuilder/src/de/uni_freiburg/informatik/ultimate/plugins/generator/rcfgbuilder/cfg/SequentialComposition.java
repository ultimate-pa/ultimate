package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
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
			Boogie2SMT boogie2smt, ModifiableGlobalVariableManager modGlobVarManager,
			boolean simplify, boolean extPqe,
			CodeBlock... codeBlocks) {
		super(source, target);
		this.m_CodeBlocks = codeBlocks;
		
		StringBuilder prettyPrinted = new StringBuilder();

		int numberCalls = 0;
		int numberReturns = 0;
		for (int i=0; i<codeBlocks.length; i++) {
			if (codeBlocks[i] instanceof InterproceduralSequentialComposition) {
				throw new IllegalArgumentException("InterproceduralSequentialComposition " +
						"must not participate in sequential compositions");
			}
			else if (codeBlocks[i] instanceof Call) {
				numberCalls++;
			} else if (codeBlocks[i] instanceof Return) {
				numberReturns++;
			} else if (codeBlocks[i] instanceof StatementSequence 
					|| codeBlocks[i] instanceof SequentialComposition
					|| codeBlocks[i] instanceof ParallelComposition
					|| codeBlocks[i] instanceof Summary) {
				//do nothing
			} else {
				throw new IllegalArgumentException("unknown CodeBlock");
			}
			codeBlocks[i].disconnectSource();
			codeBlocks[i].disconnectTarget();
			prettyPrinted.append(codeBlocks[i].getPrettyPrintedStatements());
			ModelUtils.mergeAnnotations(codeBlocks[i], this);
		}
		checkNumberOfCallsAndReturns(numberCalls, numberReturns);
		m_TransitionFormula = getInterproceduralTransFormula(boogie2smt, 
				modGlobVarManager, simplify, extPqe, false, codeBlocks);
		m_TransitionFormulaWithBranchEncoders = getInterproceduralTransFormula(
				boogie2smt, modGlobVarManager, simplify, extPqe, true, codeBlocks);
		
		m_PrettyPrinted = prettyPrinted.toString();
		updatePayloadName();
	}
	
	protected void checkNumberOfCallsAndReturns(int numberCalls, int  numberReturns) {
		if(numberCalls != numberReturns) {
			throw new IllegalArgumentException("same number of calls and returns required");
		}
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
			Boogie2SMT boogie2smt, ModifiableGlobalVariableManager modGlobVarManager,
			boolean simplify, boolean extPqe, boolean withBranchEncoders, CodeBlock... codeBlocks) {
		return getInterproceduralTransFormula(
				boogie2smt, modGlobVarManager, simplify, extPqe, withBranchEncoders, null, null, null, codeBlocks);
	}
	
	private static TransFormula getInterproceduralTransFormula(
			Boogie2SMT boogie2smt, ModifiableGlobalVariableManager modGlobVarManager,
			boolean simplify, boolean extPqe, boolean withBranchEncoders, TransFormula[] beforeCall,
			Call call, Return ret, CodeBlock... codeBlocks) {
		List<TransFormula> beforeFirstPendingCall = new ArrayList<TransFormula>();
		Call lastUnmatchedCall = null;
		int callsSinceLastUnmatchedCall = 0;
		int returnsSinceLastUnmatchedCall = 0;
		List<CodeBlock> afterLastUnmatchedCall = new ArrayList<CodeBlock>();
		for (int i = 0; i < codeBlocks.length; i++) {
			if (lastUnmatchedCall == null) {
				if (codeBlocks[i] instanceof Call) {
					lastUnmatchedCall = (Call) codeBlocks[i];
				} else {
					assert !(codeBlocks[i] instanceof Return);
					if (withBranchEncoders) {
						beforeFirstPendingCall.add(codeBlocks[i].getTransitionFormulaWithBranchEncoders());
					} else {
						beforeFirstPendingCall.add(codeBlocks[i].getTransitionFormula());
					}
				}
			} else {
				if (codeBlocks[i] instanceof Return) {
					if (callsSinceLastUnmatchedCall == returnsSinceLastUnmatchedCall) {
						Return correspondingReturn = (Return) codeBlocks[i];
						CodeBlock[] codeBlocksBetween = 
								afterLastUnmatchedCall.toArray(new CodeBlock[0]); 
						TransFormula localTransFormula = getInterproceduralTransFormula(
								boogie2smt, modGlobVarManager, simplify, extPqe, withBranchEncoders, null, lastUnmatchedCall, 
								correspondingReturn, codeBlocksBetween);
						beforeFirstPendingCall.add(localTransFormula);
						lastUnmatchedCall = null;
						callsSinceLastUnmatchedCall = 0;
						returnsSinceLastUnmatchedCall = 0;
						afterLastUnmatchedCall = new ArrayList<CodeBlock>();
					} else {
						returnsSinceLastUnmatchedCall++;
						afterLastUnmatchedCall.add(codeBlocks[i]);
					}
					assert (callsSinceLastUnmatchedCall >= returnsSinceLastUnmatchedCall);
				} else if (codeBlocks[i] instanceof Call) {
					callsSinceLastUnmatchedCall++;
					afterLastUnmatchedCall.add(codeBlocks[i]);
				} else {
					afterLastUnmatchedCall.add(codeBlocks[i]);
				}
			}
		}
		
		final TransFormula tfForCodeBlocks;
		if (lastUnmatchedCall == null) {
			assert afterLastUnmatchedCall.isEmpty();
			// no pending call in codeBlocks
			tfForCodeBlocks = TransFormula.sequentialComposition(
					boogie2smt, simplify, extPqe, beforeFirstPendingCall.toArray(new TransFormula[0]));
		} else {
			// there is a pending call in codeBlocks		
			assert (ret == null) : "no pending call between call and return possible!";
			CodeBlock[] codeBlocksBetween = afterLastUnmatchedCall.toArray(new CodeBlock[0]); 
			tfForCodeBlocks = getInterproceduralTransFormula(boogie2smt, 
					modGlobVarManager, simplify, extPqe, 
					withBranchEncoders, beforeFirstPendingCall.toArray(new TransFormula[0]), 
					lastUnmatchedCall, null, codeBlocksBetween);
		}
		
		TransFormula result;
		if (call == null) {
			assert (ret == null);
			assert (beforeCall == null);
			result = tfForCodeBlocks;
		} else {
			if (ret == null) {
				String proc = call.getCallStatement().getMethodName();
				TransFormula oldVarsAssignment = modGlobVarManager.getOldVarsAssignment(proc);
				result = TransFormula.sequentialCompositionWithPendingCall(
						boogie2smt, simplify, extPqe, beforeCall, call.getTransitionFormula(), 
						oldVarsAssignment, tfForCodeBlocks);
			} else {
				assert (beforeCall == null);
				String proc = call.getCallStatement().getMethodName();
				TransFormula oldVarsAssignment = modGlobVarManager.getOldVarsAssignment(proc);
				result = TransFormula.sequentialCompositionWithCallAndReturn(
						boogie2smt, simplify, extPqe, call.getTransitionFormula(), 
						oldVarsAssignment, tfForCodeBlocks, 
						ret.getTransitionFormula());
			}
			
		}
		return result;
	}
	
}
