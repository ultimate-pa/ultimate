package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * TestScenario for <ID | ALL>, trace has to hold: (c1, expr1), (c2, expr2), ...
 *
 * Passes iff the requirements allow the trace.
 */
public class TestScenarioPositivePattern extends TestScenarioPattern<TestScenarioPositivePattern> {

	public TestScenarioPositivePattern(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		super(scope, id, cdds, durations, durationNames);
	}

	@Override
	protected String getModality() {
		return "has to hold";
	}
}
