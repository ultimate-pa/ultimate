package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
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

public class Backtranslator extends DefaultTranslator<
					RcfgElement, ASTNode, Expression, Expression> {
	
	private Map<Statement, ASTNode> m_CodeBlock2Statement = 
			new HashMap<Statement, ASTNode>();
	


	public ASTNode putAux(Statement aux, ASTNode source) {
		return m_CodeBlock2Statement.put(aux, source);
	}


	@Override
	public List<ASTNode> translateTrace(List<RcfgElement> trace) {
		List<RcfgElement> cbTrace = trace;
		List<ASTNode> result = new ArrayList<ASTNode>();
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

	
	private void addCodeBlock(CodeBlock cb, List<ASTNode> resultTrace) {
		if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			for (Statement statement : ss.getStatements()) {
				if (m_CodeBlock2Statement.containsKey(statement)) {
					ASTNode source = m_CodeBlock2Statement.get(statement);
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
	public IProgramExecution<ASTNode, Expression> translateProgramExecution(
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
			addToFailurePath(codeBlock, trace, rcfgProgramExecution.getBranchEncoders()[i]);
			int posInNewTrace = trace.size()-1;
			ProgramState<Expression> programState = rcfgProgramExecution.getProgramState(i);
			programStateMapping.put(posInNewTrace, programState);
		}
		return boogieProgramExecution;
	}
	
	
	/**
	 * Recursive method used by getFailurePath
	 */
	private static void addToFailurePath(CodeBlock codeBlock, 
			List<Statement> trace, Map<TermVariable, Boolean> branchEncoders) {
		if (codeBlock instanceof Call) {
			Statement st = ((Call) codeBlock).getCallStatement();
			trace.add(st);
		} else if (codeBlock instanceof Return) {
			Statement st = ((Return) codeBlock).getCallStatement();
			trace.add(st);
		} else if (codeBlock instanceof Summary) {
			Statement st = ((Summary) codeBlock).getCallStatement();
			trace.add(st);
		} else if (codeBlock instanceof StatementSequence) {
			List<Statement> stmtsOfTrans = ((StatementSequence) codeBlock).getStatements();
			for (Statement st : stmtsOfTrans) {
				trace.add(st);
			}
		} else if (codeBlock instanceof SequentialComposition) {
			SequentialComposition seqComp = (SequentialComposition) codeBlock;
			for (CodeBlock cb : seqComp.getCodeBlocks()) {
				addToFailurePath(cb, trace, branchEncoders);
			}
		} else if (codeBlock instanceof ParallelComposition) {
			ParallelComposition parComp = (ParallelComposition) codeBlock;
			for (Entry<TermVariable, CodeBlock> entry  : parComp.getBranchIndicator2CodeBlock().entrySet()) {
				boolean taken = branchEncoders.get(entry.getKey());
				if(taken) {
					addToFailurePath(entry.getValue(), trace, branchEncoders);
					return;
				}
			}
			throw new AssertionError("no branch was taken");
		} else {
			throw new IllegalArgumentException("unkown code block");
		}
	}
	
	
}
