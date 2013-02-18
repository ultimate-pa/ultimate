package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

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
			Call correspondingCall = ret.getCorrespondingCallAnnot();
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
}
