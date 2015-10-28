package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.compounddomain;

import java.util.Map.Entry;

import org.apache.log4j.Logger;

import parma_polyhedra_library.Coefficient;
import parma_polyhedra_library.Constraint;
import parma_polyhedra_library.Linear_Expression_Coefficient;
import parma_polyhedra_library.Linear_Expression_Variable;
import parma_polyhedra_library.Relation_Symbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.intervaldomain.IntervalValue;

@SuppressWarnings("rawtypes")
public class IntervalToPolytopeRefinement implements IRefinement {
	private final Logger mLogger;

	public IntervalToPolytopeRefinement(Logger logger) {
		mLogger = logger;
	}

	public void refine(IAbstractState a, IAbstractState b) {
		ValueState v = null;
		PolytopeState p = null;

		if (a instanceof ValueState && b instanceof PolytopeState) {
			v = (ValueState) a;
			p = (PolytopeState) b;
		} else if (a instanceof PolytopeState && b instanceof ValueState) {
			v = (ValueState) b;
			p = (PolytopeState) a;
		} else {
			return;
		}

		for (Entry<TypedAbstractVariable, IAbstractValue<?>> entry : v
				.getEntries()) {
			if (entry.getValue() instanceof IntervalValue) {
				IntervalValue i = (IntervalValue) entry.getValue();
				{
					Rational lb = i.getValue().getLowerBound();
					if (lb.isRational() && lb.isIntegral()) {
						long val = lb.numerator().longValue()
								/ lb.denominator().longValue();
						// mLogger.debug("cutting polytobe by >= " + val);
						p.addConstraint(new Constraint(
								new Linear_Expression_Variable(p
										.getVariable(entry.getKey())),
								Relation_Symbol.GREATER_OR_EQUAL,
								new Linear_Expression_Coefficient(
										new Coefficient(val))));
					}
				}
				{
					Rational ub = i.getValue().getLowerBound();
					if (ub.isRational() && ub.isIntegral()) {
						long val = ub.numerator().longValue()
								/ ub.denominator().longValue();
						// mLogger.debug("cutting polytobe by <= " + val);
						p.addConstraint(new Constraint(
								new Linear_Expression_Variable(p
										.getVariable(entry.getKey())),
								Relation_Symbol.LESS_OR_EQUAL,
								new Linear_Expression_Coefficient(
										new Coefficient(val))));
					}
				}
			}
		}

	}
}
