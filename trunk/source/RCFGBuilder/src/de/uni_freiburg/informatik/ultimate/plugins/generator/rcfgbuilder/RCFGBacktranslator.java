package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

public class RCFGBacktranslator extends DefaultTranslator<
					RcfgElement, BoogieASTNode, Expression, Expression> {
	
	private Map<Statement, BoogieASTNode> m_CodeBlock2Statement = 
			new HashMap<Statement, BoogieASTNode>();
	


	public BoogieASTNode putAux(Statement aux, BoogieASTNode source) {
		return m_CodeBlock2Statement.put(aux, source);
	}


	@Override
	public List<BoogieASTNode> translateTrace(List<RcfgElement> trace) {
		List<RcfgElement> cbTrace = trace;
		List<BoogieASTNode> result = new ArrayList<BoogieASTNode>();
		for (RcfgElement elem : cbTrace) {
			if (elem instanceof CodeBlock) {
				addCodeBlock((CodeBlock) elem, result);
			} else if (elem instanceof ProgramPoint) {
				
			} else {
				throw new AssertionError("unknown rcfg element");
			}
		}
		return result;
	}

	
	private void addCodeBlock(CodeBlock cb, List<BoogieASTNode> resultTrace) {
		if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			for (Statement statement : ss.getStatements()) {
				if (m_CodeBlock2Statement.containsKey(statement)) {
					BoogieASTNode source = m_CodeBlock2Statement.get(statement);
					resultTrace.add(source);
				} else {
					resultTrace.add(statement);
				}
			}
		} else if (cb instanceof SequentialComposition) {
			SequentialComposition sc = (SequentialComposition) cb;
			for (CodeBlock sccb : sc.getCodeBlocks()) {
				addCodeBlock(sccb, resultTrace);
			}
		} else if (cb instanceof Call) {
			Call call = (Call) cb;
			assert call.getCallStatement() != null;
			resultTrace.add(call.getCallStatement());
		} else if (cb instanceof Return) {
			Return ret = (Return) cb;
			Call correspondingCall = ret.getCorrespondingCall();
			assert correspondingCall.getCallStatement() != null;
			resultTrace.add(correspondingCall.getCallStatement());
		} else if (cb instanceof ParallelComposition) {
			throw new UnsupportedOperationException(
					"Backtranslation of ParallelComposition not supported");
		} else {
			throw new UnsupportedOperationException(
					"Unsupported CodeBlock" + cb.getClass().getCanonicalName());
		}
	}


	@Override
	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<RcfgElement, Expression> programExecution) {
		if (!(programExecution instanceof RcfgProgramExecution)) {
			throw new IllegalArgumentException();
		}
		RcfgProgramExecution rcfgProgramExecution = (RcfgProgramExecution) programExecution;
		
		List<Statement> trace = new ArrayList<Statement>();
		Map<Integer, ProgramState<Expression>> programStateMapping = 
				new HashMap<Integer, ProgramState<Expression>>();
		BoogieProgramExecution boogieProgramExecution = 
				new BoogieProgramExecution(trace, programStateMapping);
		if (rcfgProgramExecution.getInitialProgramState() != null) {
			programStateMapping.put(-1, rcfgProgramExecution.getInitialProgramState());
		}
		for (int i=0; i<rcfgProgramExecution.getLength(); i++) {
			CodeBlock codeBlock = rcfgProgramExecution.getTraceElement(i);
			toList(codeBlock, trace, rcfgProgramExecution.getBranchEncoders()[i]);
			int posInNewTrace = trace.size()-1;
			ProgramState<Expression> programState = rcfgProgramExecution.getProgramState(i);
			programStateMapping.put(posInNewTrace, programState);
		}
		return boogieProgramExecution;
	}
	
	
	/**
	 * Transform a single (possibly large) CodeBlock to a list of Statements
	 * and add these Statements to the stList.
	 * If
	 * <ul> 
	 * <li> if the CodeBlock contains a single Statement we add this statement
	 * <li> if the CodeBlock is a StatementsSequence we add all statements
	 * <li> if the CodeBlock is a SequentialComposition we call this method
	 * recursively
	 * <li> if the CodeBlock is a ParallelComposition we ask the branchEncoders
	 * mapping on which branch we call this method recursively.
	 * If the branchEncoders mapping is null (occurs e.g., for traces whose
	 * feasibility can not be determined) we call this method recursively on
	 * some branch.
	 * </ul> 
	 */
	private static void toList(CodeBlock codeBlock, 
			List<Statement> stList, Map<TermVariable, Boolean> branchEncoders) {
		if (codeBlock instanceof Call) {
			Statement st = ((Call) codeBlock).getCallStatement();
			stList.add(st);
		} else if (codeBlock instanceof Return) {
			Statement st = ((Return) codeBlock).getCallStatement();
			stList.add(st);
		} else if (codeBlock instanceof Summary) {
			Statement st = ((Summary) codeBlock).getCallStatement();
			stList.add(st);
		} else if (codeBlock instanceof StatementSequence) {
			List<Statement> stmtsOfTrans = ((StatementSequence) codeBlock).getStatements();
			for (Statement st : stmtsOfTrans) {
				stList.add(st);
			}
		} else if (codeBlock instanceof SequentialComposition) {
			SequentialComposition seqComp = (SequentialComposition) codeBlock;
			for (CodeBlock cb : seqComp.getCodeBlocks()) {
				toList(cb, stList, branchEncoders);
			}
		} else if (codeBlock instanceof ParallelComposition) {
			ParallelComposition parComp = (ParallelComposition) codeBlock;
			Map<TermVariable, CodeBlock> bi2cb = parComp.getBranchIndicator2CodeBlock();
			if (branchEncoders == null) {
				CodeBlock someBranch = bi2cb.
						entrySet().iterator().next().getValue();
				toList(someBranch, stList, branchEncoders);
			} else {
				for (Entry<TermVariable, CodeBlock> entry  : bi2cb.entrySet()) {
					boolean taken = branchEncoders.get(entry.getKey());
					if(taken) {
						toList(entry.getValue(), stList, branchEncoders);
						return;
					}
				}
			}
			throw new AssertionError("no branch was taken");
		} else {
			throw new IllegalArgumentException("unkown code block");
		}
	}
	
	
}
