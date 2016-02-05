package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.Collection;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;

public class OctLiteralWideningOperator
		implements IAbstractStateBinaryOperator<OctagonDomainState>, OctMatrix.WideningStepSupplier {

	/**
	 * Widening steps.
	 * <p>
	 * <b>Note:</b>
	 * {@link TreeSet TreeSets} normally requires that {@code equals} is consistent with {@code compareTo(...) == 0}
	 * -- this is not the case for {@link BigDecimal} and {@link OctValue}.
	 * But the actual implementation of {@link TreeSet} (openjdk 8u40-b25) actually works in this scenario.
	 * {@code equals} is only used in methods like {@link TreeSet#contains(Object)}} or {@link TreeSet#remove(Object)}}.
	 */
	private TreeSet<OctValue> wideningSteps;
	
	public OctLiteralWideningOperator(Collection<BigDecimal> numberLiterals) {
		wideningSteps = new TreeSet<>(); // removes duplicates using method "compareTo"
		for (BigDecimal literal : numberLiterals) {			

			BigDecimal literal2 = literal.add(literal); // literal * 2, since octagons store interval bounds * 2

			wideningSteps.add(new OctValue(literal));
			wideningSteps.add(new OctValue(literal2));

			// negative literals are usually represented as UnaryExpression[ARITHNEG,<literal>]
			// => negation signs get lost during literal collection
			wideningSteps.add(new OctValue(literal.negate()));
			wideningSteps.add(new OctValue(literal2.negate()));
		}
	}

	@Override
	public OctValue nextWideningStep(OctValue v) {
		OctValue ceil = wideningSteps.ceiling(v); // TODO some programs only terminate with "higher(v)"
		return (ceil == null) ? OctValue.INFINITY : ceil;
	}
	
	@Override
	public OctagonDomainState apply(OctagonDomainState first, OctagonDomainState second) {
		return first.widen(second, (m, n) -> m.widenStepwise(n, this));
	}


}
