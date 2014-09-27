package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
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

public class RCFGBacktranslator extends DefaultTranslator<RcfgElement, BoogieASTNode, Expression, Expression> {

	public RCFGBacktranslator() {
		super(RcfgElement.class, BoogieASTNode.class, Expression.class, Expression.class);
	}

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
				addCodeBlock((CodeBlock) elem, result, null);
			} else if (elem instanceof ProgramPoint) {

			} else {
				throw new AssertionError("unknown rcfg element");
			}
		}
		return result;
	}

	
	/**
	 * Transform a single (possibly large) CodeBlock to a list of BoogieASTNodes
	 * and add these BoogieASTNodes to the List trace. If
	 * <ul>
	 * <li>if the CodeBlock contains a single Statement we add this statement
	 * <li>if the CodeBlock is a StatementsSequence we translate all Statements
	 * back to their original BoogieASTNodes (e.g., assume Statements might be
	 * translated to assert Statements, assume Statements might be translated to
	 * requires/ensures specifications)
	 * <li>if the CodeBlock is a SequentialComposition we call this method
	 * recursively
	 * <li>if the CodeBlock is a ParallelComposition we ask the branchEncoders
	 * mapping on which branch we call this method recursively. If the
	 * branchEncoders mapping is null (occurs e.g., for traces whose feasibility
	 * can not be determined) we call this method recursively on some branch.
	 * </ul>
	 */
	private void addCodeBlock(CodeBlock cb, List<BoogieASTNode> trace, 
			Map<TermVariable, Boolean> branchEncoders) {
		if (cb instanceof Call) {
			Statement st = ((Call) cb).getCallStatement();
			trace.add(st);
		} else if (cb instanceof Return) {
			Statement st = ((Return) cb).getCallStatement();
			trace.add(st);
		} else if (cb instanceof Summary) {
			Statement st = ((Summary) cb).getCallStatement();
			trace.add(st);
		} else if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			for (Statement statement : ss.getStatements()) {
				if (m_CodeBlock2Statement.containsKey(statement)) {
					BoogieASTNode source = m_CodeBlock2Statement.get(statement);
					trace.add(source);
				} else {
					trace.add(statement);
				}
			}
		} else if (cb instanceof SequentialComposition) {
			SequentialComposition seqComp = (SequentialComposition) cb;
			for (CodeBlock sccb : seqComp.getCodeBlocks()) {
				addCodeBlock(sccb, trace, branchEncoders);
			}
		} else if (cb instanceof ParallelComposition) {
			ParallelComposition parComp = (ParallelComposition) cb;
			Map<TermVariable, CodeBlock> bi2cb = parComp.getBranchIndicator2CodeBlock();
			if (branchEncoders == null) {
				CodeBlock someBranch = bi2cb.entrySet().iterator().next().getValue();
				addCodeBlock(someBranch, trace, branchEncoders);
			} else {
				for (Entry<TermVariable, CodeBlock> entry : bi2cb.entrySet()) {
					boolean taken = branchEncoders.get(entry.getKey());
					if (taken) {
						addCodeBlock(entry.getValue(), trace, branchEncoders);
						return;
					}
				}
			}
			throw new AssertionError("no branch was taken");
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

		List<BoogieASTNode> trace = new ArrayList<BoogieASTNode>();
		Map<Integer, ProgramState<Expression>> programStateMapping = 
				new HashMap<Integer, ProgramState<Expression>>();
		BoogieProgramExecution boogieProgramExecution = 
				new BoogieProgramExecution(trace, programStateMapping);
		if (rcfgProgramExecution.getInitialProgramState() != null) {
			programStateMapping.put(-1, rcfgProgramExecution.getInitialProgramState());
		}
		for (int i = 0; i < rcfgProgramExecution.getLength(); i++) {
			CodeBlock codeBlock = rcfgProgramExecution.getTraceElement(i);
			addCodeBlock(codeBlock, trace, rcfgProgramExecution.getBranchEncoders()[i]);
			int posInNewTrace = trace.size() - 1;
			ProgramState<Expression> programState = rcfgProgramExecution.getProgramState(i);
			programStateMapping.put(posInNewTrace, programState);
		}
		return boogieProgramExecution;
	}



}
