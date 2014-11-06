package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.*;

/**
 * Substitute the identifiers inside an AST of a Promela Büchi automaton
 * description by the correct atomic propositions.
 * 
 * @author Langenfeld
 * 
 */
public class SubstituteAPVisitor {

	private final Map<String, AstNode> mAP2AST;
	private final List<Name> mSubstituteNames;
	private final List<AstNode> mSubstituteParents;

	/**
	 * Go visit and replace
	 * 
	 * @param aps
	 *            : map ident->Ast of the atomic propositions
	 * @param ast
	 *            : ast of the Promela description of the Büchi automaton
	 */
	public SubstituteAPVisitor(Map<String, AstNode> aps, AstNode ast) {
		mSubstituteNames = new ArrayList<Name>();
		mSubstituteParents = new ArrayList<AstNode>();
		mAP2AST = aps;
		visit(ast, null);

		// now substitute idents by asts at the occurences the visitor has found
		for (int i = 0; i < mSubstituteNames.size(); i++) {
			if (mSubstituteParents.get(i) instanceof OptionStatement) {
				((OptionStatement) mSubstituteParents.get(i)).setCondition(mAP2AST.get(mSubstituteNames.get(i)
						.getIdent()));
			} else {
				mSubstituteParents.get(i).removeOutgoing(mSubstituteNames.get(i));
				mSubstituteParents.get(i).addOutgoing(mAP2AST.get(mSubstituteNames.get(i).getIdent()));
			}
		}
	}

	/*
	 * search for all occurences of an identiefier known to be an atomic
	 * proposition
	 */
	private void visit(AstNode node, AstNode parent) {
		if (node instanceof BoolLiteral) {
			return;
		} else if (node instanceof Name) {
			// int literal may not occure
			Name n = (Name) node;
			if (mAP2AST.containsKey(n.getIdent())) {
				mSubstituteNames.add(n);
				mSubstituteParents.add(parent);
			}
		} else if (node instanceof OptionStatement) {
			visit(((OptionStatement) node).getCondition(), node);
		} else {
			// blindly visit everything else
			for (AstNode a : node.getOutgoingNodes())
				visit(a, node);
		}
	}

}
