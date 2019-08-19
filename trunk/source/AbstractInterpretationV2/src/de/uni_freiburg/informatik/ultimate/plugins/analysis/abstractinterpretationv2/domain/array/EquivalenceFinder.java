package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AbstractGeneralizedaAffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class EquivalenceFinder {
	private final Script mScript;
	private final Set<AffineRelation> mRelations;

	public EquivalenceFinder(final Term term, final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mScript = mgdScript.getScript();
		final Term cnf =
				SmtUtils.toCnf(services, mgdScript, term, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mRelations = getEquivalenceRelations(cnf);
	}

	public UnionFind<Term> getEquivalences(final Set<? extends Term> neededEquivalenceClasses) {
		final UnionFind<Term> result = new UnionFind<>();
		for (final AffineRelation relation : mRelations) {
			for (final Term var : neededEquivalenceClasses) {
				final SolvedBinaryRelation sbr = relation.solveForSubject(mScript, var);
				if (sbr == null || !sbr.getAssumptionsMap().isEmpty()) {
					continue;
				}
				assert "=".equals(relation.getRelationSymbol().toString());
				final Term equivalent = sbr.getRightHandSide();
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
		for (final Term conjunct : SmtUtils.getConjuncts(term)) {
			final AffineRelation relation = AffineRelation.convert(mScript, conjunct, TransformInequality.STRICT2NONSTRICT);
			if (relation == null) {
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
				final AffineTerm affine2 = normalize(AffineTerm.mul(relation.getAffineTerm(), Rational.MONE));
				final AffineTerm positive = symbol == RelationSymbol.LEQ ? affine1 : affine2;
				final AffineTerm negative = symbol == RelationSymbol.LEQ ? affine2 : affine1;
				if (leqTerms.contains(negative)) {
					leqTerms.remove(negative);
					result.add(new AffineRelation(mScript, positive, RelationSymbol.EQ));
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

	private static AffineTerm normalize(final AffineTerm affineTerm) {
		Rational factor = affineTerm.getConstant();
		for (final Rational r : affineTerm.getVariable2Coefficient().values()) {
			factor = factor.gcd(r);
		}
		if (factor.equals(Rational.ZERO)) {
			return affineTerm;
		}
		return AffineTerm.mul(affineTerm, factor.inverse());
	}
}
