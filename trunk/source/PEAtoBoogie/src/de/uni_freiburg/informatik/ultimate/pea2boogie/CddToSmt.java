package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.SingleTermResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;


public class CddToSmt{ 

	private final Script mScript;
	private final Term mTrue;
	private final Term mFalse;
	private final Map<String, IProgramNonOldVar> mVars;
	private final IIdentifierTranslator[] mIdentifierTranslators;
	private final IReqSymbolExpressionTable mBoogieSymboltable;
	private final Boogie2SMT mBoogieToSmt;

	public CddToSmt(final IUltimateServiceProvider services, final IToolchainStorage storage, 
			final Script script, final Boogie2SMT boogieToSmt,
			final BoogieDeclarations boogieDeclarations, final IReqSymbolExpressionTable symboltable ) {
		mScript = script;
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
		mBoogieToSmt = boogieToSmt;
		mVars = mBoogieToSmt.getBoogie2SmtSymbolTable().getGlobalsMap();
		mIdentifierTranslators = new IIdentifierTranslator[] { this::getSmtIdentifier };
		mBoogieSymboltable = symboltable;
	}
	
	public Term toSmt(final Expression expr) {
		final SingleTermResult result = mBoogieToSmt.getExpression2Term().translateToTerm(mIdentifierTranslators, expr);
		return result.getTerm();
	}

	public Term toSmt(final CDD cdd) {
		if (cdd == CDD.TRUE) {
			return mTrue;
		}
		if (cdd == CDD.FALSE) {
			return mFalse;
		}
		final CDD simplifiedCdd = cdd.getDecision().simplify(cdd.getChilds());
		if (simplifiedCdd == CDD.TRUE) {
			return mTrue;
		}
		if (simplifiedCdd == CDD.FALSE) {
			return mFalse;
		}
		final CDD[] childs = simplifiedCdd.getChilds();
		final Decision<?> decision = simplifiedCdd.getDecision();

		Term rtr = null;
		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}
			Term childTerm = toSmt(childs[i]);
			if (!simplifiedCdd.childDominates(i)) {
				Term decisionTerm;

				if (decision instanceof RangeDecision) {
					// TODO: I added negation by restructuring, is this wrong?
					decisionTerm = toSmtForRange(i, decision.getVar(), ((RangeDecision) decision).getLimits());
				} else if (decision instanceof BoogieBooleanExpressionDecision) {
					// rewrite expression s.t. identifier expressions have declarations
					final Expression expr = ((BoogieBooleanExpressionDecision) decision).getExpression();
					final AddDeclarationInformationToIdentifiers visitor = new AddDeclarationInformationToIdentifiers();
					final Expression transformedExpr = expr.accept(visitor);
					decisionTerm = toSmt(transformedExpr);
				} else if (decision instanceof BooleanDecision) {
					// TODO: This also covers RelationDecisions, is this intended?
					decisionTerm = getTermVarTerm(((BooleanDecision) decision).getVar());
				} else if (decision instanceof EventDecision) {
					decisionTerm = getTermVarTerm(((EventDecision) decision).getVar());
				} else {
					throw new UnsupportedOperationException("Unknown decision type: " + decision.getClass());
				}

				if (i == 1 && !(decision instanceof RangeDecision)) {
					// negate if right child
					decisionTerm = SmtUtils.not(mScript, decisionTerm);
				}

				if (childTerm == mTrue) {
					childTerm = decisionTerm;
				} else {
					childTerm = SmtUtils.and(mScript, decisionTerm, childTerm);
				}
			}
			if (rtr == null) {
				rtr = childTerm;
			} else {
				rtr = SmtUtils.or(mScript, childTerm, rtr);
			}
		}

		if (rtr == null) {
			return mFalse;
		}
		return rtr;
	}
	
	private Term toSmtForRange(final int childIdx, final String varname, final int[] limits) {
		final Term var = getTermVarTerm(varname);

		if (childIdx == 0) {
			// only upper bound
			final Term rhs = mScript.decimal(Double.toString(limits[0] / 2));
			if ((limits[0] & 1) == 0) {
				// strict because of first bit encoding
				return SmtUtils.less(mScript, var, rhs);
			}
			// not strict
			return SmtUtils.leq(mScript, var, rhs);
		}

		// TODO: Why can the limit be one larger than the array?
		if (childIdx == limits.length) {
			// only lower bound
			final Term rhs = mScript.decimal(Double.toString(limits[limits.length - 1] / 2));
			if ((limits[limits.length - 1] & 1) == 1) {
				return SmtUtils.greater(mScript, var, rhs);
			}
			return SmtUtils.geq(mScript, var, rhs);
		}

		if (limits[childIdx - 1] / 2 == limits[childIdx] / 2) {
			// we have upper and lower, but they are identical, so its EQ
			// and they differ in the first bit because first bit encoding and sortedness
			final Term rhs = mScript.decimal(Double.toString(limits[childIdx] / 2));
			return SmtUtils.binaryEquality(mScript, var, rhs);
		}

		// we have upper and lower bounds
		final Term lb = mScript.decimal(Double.toString(limits[childIdx - 1] / 2));
		final Term ub = mScript.decimal(Double.toString(limits[childIdx] / 2));

		final Term lbTerm;
		final Term ubTerm;
		if ((limits[childIdx - 1] & 1) == 1) {
			// strict lb
			lbTerm = SmtUtils.less(mScript, lb, var);
		} else {
			lbTerm = SmtUtils.leq(mScript, lb, var);
		}

		if ((limits[childIdx] & 1) == 0) {
			// strict ub
			ubTerm = SmtUtils.less(mScript, var, ub);
		} else {
			ubTerm = SmtUtils.leq(mScript, var, ub);
		}
		return SmtUtils.and(mScript, lbTerm, ubTerm);
	}



	private Term getSmtIdentifier(final String id, final DeclarationInformation declInfo, final boolean isOldContext,
			final BoogieASTNode boogieASTNode) {
		if (isOldContext || declInfo != DeclarationInformation.DECLARATIONINFO_GLOBAL) {
			throw new UnsupportedOperationException();
		}
		return getTermVarTerm(id);
	}
	
	public Term getTermVarTerm(final String name) {
		final IProgramNonOldVar termVar = mVars.get(name);
		return termVar.getTerm();
	}
	
	
	private final class AddDeclarationInformationToIdentifiers extends GeneratedBoogieAstTransformer {

		@Override
		public Expression transform(final IdentifierExpression node) {
			return mBoogieSymboltable.getIdentifierExpression(node.getIdentifier());
		}

	}

}
