package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class EquivalenceFinder {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;

	public EquivalenceFinder(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mServices = services;
		mMgdScript = mgdScript;
	}

	public UnionFind<Term> getEquivalences(final Term term, final Set<Term> neededEquivalenceClasses) {
		final Term cnf =
				SmtUtils.toCnf(mServices, mMgdScript, term, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final UnionFind<Term> result = new UnionFind<>();
		for (final AffineRelation relation : getEquivalenceRelations(cnf)) {
			for (final Term var : neededEquivalenceClasses) {
				if (!relation.isVariable(var)) {
					continue;
				}
				final ApplicationTerm lhsTerm;
				try {
					lhsTerm = relation.onLeftHandSideOnly(mMgdScript.getScript(), var);
				} catch (final NotAffineException e) {
					continue;
				}
				assert "=".equals(lhsTerm.getFunction().getApplicationString());
				final Term equivalent = lhsTerm.getParameters()[1];
				result.findAndConstructEquivalenceClassIfNeeded(var);
				result.findAndConstructEquivalenceClassIfNeeded(equivalent);
				result.union(var, equivalent);
			}
		}
		return result;
	}

	private Set<AffineRelation> getEquivalenceRelations(final Term term) {
		final Set<AffineRelation> result = new HashSet<>();
		final Set<AffineTerm> leqTerms = new HashSet<>();
		final Script script = mMgdScript.getScript();
		for (final Term conjunct : SmtUtils.getConjuncts(term)) {
			final AffineRelation relation;
			try {
				relation = new AffineRelation(script, conjunct, TransformInequality.STRICT2NONSTRICT);
			} catch (final NotAffineException e) {
				continue;
			}
			final RelationSymbol symbol = relation.getRelationSymbol();
			switch (symbol) {
			case EQ:
				result.add(relation);
				break;
			case LEQ:
			case GEQ:
				final AffineTerm affine1 = normalize(relation.getAffineTerm());
				final AffineTerm affine2 = normalize(new AffineTerm(relation.getAffineTerm(), Rational.MONE));
				final AffineTerm positive = symbol == RelationSymbol.LEQ ? affine1 : affine2;
				final AffineTerm negative = symbol == RelationSymbol.LEQ ? affine2 : affine1;
				if (leqTerms.contains(negative)) {
					leqTerms.remove(negative);
					// TODO: Is there a more efficient way to get an AffineRelation from an AffineTerm and a
					// RelationSymbol?
					final Term equality = SmtUtils.binaryEquality(script, positive.toTerm(script), script.numeral("0"));
					try {
						result.add(new AffineRelation(script, equality, TransformInequality.STRICT2NONSTRICT));
					} catch (final NotAffineException e) {
						continue;
					}
				} else {
					leqTerms.add(positive);
				}
				break;
			default:
				break;
			}
		}
		return result;
	}

	private AffineTerm normalize(final AffineTerm affineTerm) {
		Rational factor = affineTerm.getConstant();
		for (final Rational r : affineTerm.getVariable2Coefficient().values()) {
			factor = factor.gcd(r);
		}
		if (factor.equals(Rational.ZERO)) {
			return affineTerm;
		}
		return new AffineTerm(affineTerm, factor.inverse());
	}
}
