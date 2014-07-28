package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class RDCodeBlockWrapper {
	
	CodeBlock mCodeBlock;
	

	public RDCodeBlockWrapper(CodeBlock cb) {
		mCodeBlock = cb;
		generateUsesAndDefs(cb);
	}


	private void generateUsesAndDefs(CodeBlock cb) {
//		if (cb instanceof SequentialComposition) {
//			SequentialComposition sc = (SequentialComposition) cb;
//			for(CodeBlock subCB : sc.getCodeBlocks()) {
//				generateUsesAndDefs(subCB);
//			}
//		} else 
		if (cb instanceof SequentialComposition) {
			throw new AssertionError("Large block encoding not allowed right now");
		}
		if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			for (Statement stm : ss.getStatements()) {
				TreeSet<String> uses = getUses(stm);
				TreeSet<String> defs = getDefs(stm);
			}
		} else {
			
		}
	}


	private TreeSet<String> getDefs(Statement stm) {
		TreeSet<String> toReturn = new TreeSet<String>();
		if (stm instanceof AssignmentStatement) {
			AssignmentStatement as = (AssignmentStatement) stm;
			for (LeftHandSide lhs : as.getLhs()) {
				assert lhs instanceof VariableLHS : "we don't support structs or arrays right now";
				VariableLHS vlhs = (VariableLHS) lhs;
				toReturn.add(vlhs.getIdentifier());
			}
		} else if (stm instanceof AssumeStatement) {
			AssumeStatement as = (AssumeStatement) stm;
			toReturn.addAll(extractIdentifiersFromExpression(as.getFormula())); //FIXME: this is unclear..
		} else {
		}
		return toReturn;
	}


	private TreeSet<String> getUses(Statement stm) {
		TreeSet<String> toReturn = new TreeSet<String>();
		if (stm instanceof AssignmentStatement) {
			AssignmentStatement as = (AssignmentStatement) stm;
			for (Expression ex : as.getRhs()) {
				toReturn.addAll(extractIdentifiersFromExpression(ex));
			}
		} else if (stm instanceof AssumeStatement) {
			AssumeStatement as = (AssumeStatement) stm;
			toReturn.addAll(extractIdentifiersFromExpression(as.getFormula()));
		} else {
		}
		return toReturn;
	}


	private List<String> extractIdentifiersFromExpression(Expression ex) {
		ArrayList<String> toReturn = new ArrayList<String>();
		if (ex instanceof IdentifierExpression) {
			toReturn.add(((IdentifierExpression) ex).getIdentifier());
		} else if (ex instanceof UnaryExpression) {
			UnaryExpression uex = (UnaryExpression) ex;
			toReturn.addAll(extractIdentifiersFromExpression(uex.getExpr()));
		} else if (ex instanceof BinaryExpression) {
			BinaryExpression bex = (BinaryExpression) ex;
			toReturn.addAll(extractIdentifiersFromExpression(bex.getLeft()));
			toReturn.addAll(extractIdentifiersFromExpression(bex.getRight()));
		}
		return toReturn;
	}
	
	
}
