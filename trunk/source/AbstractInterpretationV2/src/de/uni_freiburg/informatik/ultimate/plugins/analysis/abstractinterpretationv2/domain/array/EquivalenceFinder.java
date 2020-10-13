package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class EquivalenceFinder {
	private final Script mScript;
	private final Set<PolynomialRelation> mRelations;

	public EquivalenceFinder(final Term term, final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mScript = mgdScript.getScript();
		final Term cnf =
				SmtUtils.toCnf(services, mgdScript, term, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mRelations = getEquivalenceRelations(cnf);
	}

	public UnionFind<Term> getEquivalences(final Set<? extends Term> neededEquivalenceClasses) {
		final UnionFind<Term> result = new UnionFind<>();
		for (final PolynomialRelation relation : mRelations) {
			for (final Term var : neededEquivalenceClasses) {
				final SolvedBinaryRelation sbr = relation.solveForSubject(mScript, var);
				if (sbr == null) {
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

	private Set<PolynomialRelation> getEquivalenceRelations(final Term term) {
		final Set<PolynomialRelation> result = new HashSet<>();
		final Set<AffineTerm> leqTerms = new HashSet<>();
		for (final Term conjunct : SmtUtils.getConjuncts(term)) {
			final PolynomialRelation polyRel = PolynomialRelation.convert(mScript, conjunct, TransformInequality.STRICT2NONSTRICT);
			if (polyRel == null) {
				continue;
			}
			final RelationSymbol symbol = polyRel.getRelationSymbol();
			switch (symbol) {
			case EQ:
				result.add(polyRel);
				break;
			case LEQ:
			case GEQ:
				final AffineTerm affine1 = normalize((AffineTerm) polyRel.getPolynomialTerm());
				final AffineTerm affine2 = normalize(AffineTerm.mul(polyRel.getPolynomialTerm(), Rational.MONE));
				final AffineTerm positive = symbol == RelationSymbol.LEQ ? affine1 : affine2;
				final AffineTerm negative = symbol == RelationSymbol.LEQ ? affine2 : affine1;
				if (leqTerms.contains(negative)) {
					leqTerms.remove(negative);
					result.add(new PolynomialRelation(mScript, positive, RelationSymbol.EQ));
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
