/*
 * Copyright (C) 2010-2018 Amalinda Oertel
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-srParse plug-in.
 *
 * The ULTIMATE Library-srParse plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-srParse plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-srParse plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-srParse plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-srParse plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;

/**
 * The class <code>PatternToPEA</code> offers functionality to transform requirements, formalized as instantiated
 * Patterns, via Countertraces (ct) to PEAS.
 *
 *
 * @author Amalinda Oertel April 2010
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
 * @deprecated Should be done directly in the pattern
 */

@Deprecated
public class PatternToPEA {
	private final Trace2PeaCompiler mCompiler;
	private final ILogger mLogger;

	// this index is needed so that the counters in the peas for the quantitative patterns
	// do not have the same names
	private int mNameIndex = 0;

	public PatternToPEA(final ILogger logger, final Set<String> ignoredIds) {
		mLogger = logger;
		mCompiler = new Trace2PeaCompiler(logger, ignoredIds);
	}

	public PhaseEventAutomata compile(final String id, final CounterTrace ct) {
		mNameIndex++;
		return mCompiler.compile(id + "_" + mNameIndex, ct);
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// AbsencePattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata absencePattern(final String id, final CDD P, final CDD Q, final CDD R,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), phase(P), phaseTrue() });
			ctA = mCompiler.compile(id + "_AbsenceGlob", ct);
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()), phaseTrue() });
			ctA = mCompiler.compile(id + "_AbsenceBefore", ct);
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_AbsenceUntil", ct);
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), phase(Q), phaseTrue(), phase(P), phaseTrue() });
			ctA = mCompiler.compile(id + "_AbsenceAfter", ct);
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(Q.and(R.negate())),
							new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(P.and(R.negate())),
							new CounterTrace.DCPhase(R.negate()), phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_AbsenceBetween", ct);
			return ctA;
		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Existence Pattern
	// muß noch für 3scopes erweitert werden
	// Scope Globally
	public PhaseEventAutomata existencePattern(final String id, final CDD P, final CDD Q, final CDD R,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			mLogger.error("Existence-Globally: method incomplete");
			// CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
			// new CounterTrace.DCPhase(P.negate()),
			// new CounterTrace.DCPhase(),
			// new CounterTrace.DCPhase()
			// });
			// ctA = compiler.compile("ExistenceGlob", ct); ctA.dump();
			// return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
					new CounterTrace.DCPhase(P.negate().and(R.negate())), phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_TExistenceBefore", ct);
			return ctA;
		} else if (scope.contains("until")) {
			mLogger.error("Existence-Until: method incomplete");
		} else if (scope.contains("After")) {
			mLogger.error("Existence-After: method incomplete");
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(Q.and(R.negate())),
							new CounterTrace.DCPhase(P.negate().and(R.negate())), phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_TExistenceBetween", ct);
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Bounded Existence Pattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata bndExistencePattern(final String id, final CDD P, final CDD Q, final CDD R,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), phase(P), new CounterTrace.DCPhase(P.negate()), phase(P),
							new CounterTrace.DCPhase(P.negate()), phase(P), phaseTrue() });
			ctA = mCompiler.compile(id + "_BndExistenceGlob", ct);
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_TBndExistenceBefore", ct);
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()), phaseTrue() });
			ctA = mCompiler.compile(id + "_TBndExistenceUntil", ct);
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), phase(Q), phaseTrue(),
					phase(P), new CounterTrace.DCPhase(P.negate()), phase(P), new CounterTrace.DCPhase(P.negate()),
					phase(P), phaseTrue() });
			ctA = mCompiler.compile(id + "_TBndExistenceAfter", ct);
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()), phase(R),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_TBndExistenceBetween", ct);
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Precedence Pattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata precedencePattern(final String id, final CDD P, final CDD Q, final CDD R, final CDD S,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(S.negate()), phase(P), phaseTrue() });
			ctA = mCompiler.compile(id + "_precedenceGlob", ct);
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct =
					new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate().and(S.negate())),
							new CounterTrace.DCPhase(P.and(R.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_precedenceBefore", ct);
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate()).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(P.and(R.negate())),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_precedenceUntil", ct);
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(Q.and(S.negate())),
							new CounterTrace.DCPhase(S.negate()), phase(P), phaseTrue() });
			ctA = mCompiler.compile(id + "_precedenceAfter", ct);
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(S.negate()).and(R.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())), new CounterTrace.DCPhase(R.negate()),
					phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_precBet", ct);
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Precedence Chain Pattern 12
	// Scope Globally
	public PhaseEventAutomata precedenceChainPattern12(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final CDD T, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
					phase(S), phaseTrue(), phase(T), phaseTrue() });
			ctA = mCompiler.compile(id + "_precCh12G", ct);
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(S.and(R.negate()).and(P.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_precCh12B", ct);
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_precCh12U", ct);
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(Q.and(P.negate())), new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(S.and(P.negate())), phaseTrue(), phase(T), phaseTrue() });
			ctA = mCompiler.compile(id + "_precCh12A", ct);
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(R.negate()), phase(R),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_precCh12Bet", ct);
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Precedence Chain Pattern 21
	// Scope Globally
	// Klappt noch gar nicht
	public PhaseEventAutomata precedenceChainPattern21(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final CDD T, final String scope) {
		PhaseEventAutomata ctA, ctA1;
		final PhaseEventAutomata ctA2, ctA3;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(S.negate()),
					new CounterTrace.DCPhase(S.and(T.negate())), new CounterTrace.DCPhase(T.negate()), phase(P),
					phaseTrue() });

			final CounterTrace ct1 = new CounterTrace(
					new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(T.negate()), phase(P), phaseTrue() });

			// CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] {
			// new CounterTrace.DCPhase(S.and(T.negate())),
			// new CounterTrace.DCPhase(T.negate()),
			// new CounterTrace.DCPhase(P),
			// new CounterTrace.DCPhase()
			// });

			ctA1 = mCompiler.compile(id + "_precCh21G", ct1); // ctA1.dump();

			ctA = mCompiler.compile(id + "_precCh21G2", ct);
			// ctA = (ctA).parallel(ctA1);

			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = counterTrace(phaseTrue());

			mLogger.error("precedenceChainPattern21 Before: method incomplete");
			ctA = mCompiler.compile(id + "_precCh12B", ct);
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = counterTrace(phaseTrue());
			mLogger.error("precedenceChainPattern21 Until: method incomplete");
			ctA = mCompiler.compile(id + "_precCh12U", ct);
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = counterTrace(phaseTrue());
			mLogger.error("precedenceChainPattern21 After: method incomplete");
			ctA = mCompiler.compile(id + "_precCh12A", ct);
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = counterTrace(phaseTrue());
			mLogger.error("precedenceChainPattern21 Between: method incomplete");
			ctA = mCompiler.compile(id + "_precCh12Bet", ct);
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Response Chain Pattern 21
	// Scope Globally
	// Klappt noch gar nicht
	public PhaseEventAutomata responseChainPattern21(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final CDD T, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA1, ctA2, ctA3;
		if (scope.contains("Globally")) {
			final CounterTrace ct = counterTrace(phaseTrue());

			ctA = mCompiler.compile(id + "_respCh21G", ct);
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(S.and(R.negate()).and(T.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_respCh21B", ct);
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = counterTrace(phaseTrue());
			ctA = mCompiler.compile(id + "_respCh21U", ct);
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = counterTrace(phaseTrue());
			ctA = mCompiler.compile(id + "_respCh21A", ct);
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(S.and(R.negate()).and(T.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_respCh21Bet", ct);
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	public PhaseEventAutomata responseChainPattern12(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final CDD T, final String requestedLogic) {
		mLogger.error("responseChainPattern12: method incomplete");
		PhaseEventAutomata ctA;
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// minimum Duration Pattern
	// komplett und validiert
	public PhaseEventAutomata minDurationPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct =
					new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(P.negate()),
							new CounterTrace.DCPhase(P, CounterTrace.BOUND_LESS, timebound),
							new CounterTrace.DCPhase(P.negate()), phaseTrue() });
			return compile(id + "_minDurG", ct);
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R.negate().and(P.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(R.negate().and(P.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_minDurB" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(Q.and(R.negate())),
							new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(P.negate().and(R.negate())),
							new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
							new CounterTrace.DCPhase(R.negate().and(P.negate())), new CounterTrace.DCPhase(R.negate()),
							phaseTrue() });
			ctA = mCompiler.compile(id + "_minDurU" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), phase(Q), phaseTrue(),
					new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(P.negate()), phaseTrue() });
			ctA = mCompiler.compile(id + "_minDurA" + mNameIndex, ct);
			mNameIndex++;

			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(Q.and(R.negate())),
							new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(P.negate().and(R.negate())),
							new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
							new CounterTrace.DCPhase(R.negate().and(P.negate())), new CounterTrace.DCPhase(R.negate()),
							phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_minDurBetween" + mNameIndex, ct);
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// maximum Duration Pattern
	// in Entwicklung
	public PhaseEventAutomata maxDurationPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		// mit der auskommentierten Zeile sind wir näher an der Semantik von Konrad/Cheng, aber in der Benutzung ist
		// diese Version die einfachere
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					// new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, timebound), phaseTrue()

			});
			ctA = mCompiler.compile(id + "_maxDurG" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R.negate().and(P.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_maxDurB" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_maxDurU" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), phase(Q), phaseTrue(),
					new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, timebound), phaseTrue() });
			ctA = mCompiler.compile(id + "_maxDurA" + mNameIndex, ct);
			mNameIndex++;

			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct =
					new CounterTrace(
							new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(Q.and(R.negate())),
									new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(P.and(R.negate()),
											CounterTrace.BOUND_GREATEREQUAL, timebound),
									new CounterTrace.DCPhase(R.negate()), phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_maxDurBet" + mNameIndex, ct);
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Response Pattern
	// (außer between) validiert
	public PhaseEventAutomata bndResponsePattern(final String id, final CDD R, final CDD P, final CDD Q, final CDD S,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(R.and(S.negate())),
							new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, timebound), phaseTrue() });
			ctA = mCompiler.compile(id + "_bndResG" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(Q.negate()),
					new CounterTrace.DCPhase(Q.negate().and(R).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(Q.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_bndResB" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(P.and(Q.negate())), new CounterTrace.DCPhase(Q.negate()),
					new CounterTrace.DCPhase(R.and(Q.negate()).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(Q.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_bndResU" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), phase(P), phaseTrue(),
					new CounterTrace.DCPhase(R.and(S.negate())),
					new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATEREQUAL, timebound), phaseTrue() });
			ctA = mCompiler.compile(id + "_bndResA" + mNameIndex, ct);
			mNameIndex++;

			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(P.and(Q.negate())), new CounterTrace.DCPhase(Q.negate()),
					new CounterTrace.DCPhase(R.and(Q.negate()).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(Q.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					new CounterTrace.DCPhase(Q.negate()), phase(Q), phaseTrue() });
			ctA = mCompiler.compile(id + "_bndResBet" + mNameIndex, ct);
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// periodic Pattern
	// komplett und validiert
	public PhaseEventAutomata periodicPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_GREATER, 10), phaseTrue() });
			ctA = mCompiler.compile(id + "_periG" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_periB" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					phaseTrue() });
			ctA = mCompiler.compile(id + "_periU" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), phase(Q), phaseTrue(),
					new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_GREATER, timebound), phaseTrue() });
			ctA = mCompiler.compile(id + "_periA" + mNameIndex, ct);
			mNameIndex++;

			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(R.negate()), phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_periBet" + mNameIndex, ct);
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// response Pattern
	// NICHT komplett und validiert
	/**
	 * ... it is always the case that if P holds then S eventually holds.
	 *
	 * @param id
	 *            The id of the requirement.
	 * @param P
	 *            The P observable of the pattern.
	 * @param Q
	 *            First scope observable
	 * @param R
	 *            Second scope observable
	 * @param S
	 *            The S observable of the pattern.
	 * @param scope
	 *            The scope of the requirement as a string.
	 * @return A {@link PhaseEventAutomata} that represents this requirement.
	 */
	public PhaseEventAutomata responsePattern(final String id, final CDD P, final CDD Q, final CDD R, final CDD S,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			// Globally, it is always the case that if P holds then S eventually holds.
			// (¬(true;|P ∧ ¬S|;|¬S|)) -> true
			assert Q == null && R == null : "Globally does not allow scope observables";
			// TODO: Amalinda schrieb: hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des
			// intervalls gelten
			// TODO: Das leads-to scheint falsch
			final CounterTrace ct = counterTrace(phaseTrue(), phase(P.and(S.negate())), phase(S.negate()), phaseTrue());
			mLogger.warn(id + " responsePattern globally: method not validated");
			ctA = mCompiler.compile(id + "_respG", ct);
			return ctA;
		} else if (scope.contains("Before")) {
			// Before Q, it is always the case that if P holds then S eventually holds.
			// ¬(|¬Q|;|P ∧ ¬S ∧ ¬Q|;|¬S ∧ ¬Q|;|Q|; true)
			assert P != null;
			final CounterTrace ct = counterTrace(phase(R.negate()), phase(P.and(R.negate()).and(S.negate())),
					phase(S.negate().and(R.negate())), phase(R), phaseTrue());
			ctA = mCompiler.compile(id + "_respB", ct);
			return ctA;
		} else if (scope.contains("until")) {
			// TODO: Amalinda schrieb: hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des
			// intervalls gelten
			final CounterTrace ct = counterTrace(phaseTrue());
			mLogger.error(id + " responsePattern until: method incomplete");
			ctA = mCompiler.compile(id + "_respU", ct);
			return ctA;
		} else if (scope.contains("After")) {
			// (¬(true;|Q|;true;|P ∧ ¬S|;|¬S|)) -> true
			// TODO: Amalinda schrieb: hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des
			// intervalls gelten
			final CounterTrace ct = counterTrace(phaseTrue());
			mLogger.error(id + " responsePattern after: method incomplete");
			ctA = mCompiler.compile(id + "_respA", ct);
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
					new CounterTrace.DCPhase(R.negate().and(S.negate())), phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_respBet", ct);
			return ctA;

		}
		assert false : "No known scope";
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Entry Condition Pattern
	public PhaseEventAutomata bndEntryConditionPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate()), phaseTrue() });
			ctA = mCompiler.compile(id + "_inv1" + mNameIndex, ct);
			mNameIndex++;

			return ctA;
			// return mctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_inv" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {

					phaseTrue(), new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), phaseTrue() });
			ctA = mCompiler.compile(id + "_inv" + mNameIndex, ct);
			mNameIndex++;

			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), phase(Q), phaseTrue(),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate()), phaseTrue() });
			ctA = mCompiler.compile(id + "_inv" + mNameIndex, ct);
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					phase(R), phaseTrue() });
			ctA = mCompiler.compile(id + "_inv" + mNameIndex, ct);
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = counterTrace(phaseTrue());
		ctA = mCompiler.compile(id + "_NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// invariant Pattern
	// validiert
	public PhaseEventAutomata invariantPattern(final String id, final CDD P, final CDD Q, final CDD R, final CDD S,
			final String scope) {
		PhaseEventAutomata ctA;
		ctA = absencePattern(id, P.and(S.negate()), Q, R, scope);
		return ctA;

	}

	// //Scope Before R
	// public PhaseEventAutomata absencePattern_Before(CDD P, CDD R, String scope) {
	// PhaseEventAutomata ctA;
	// CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	// new CounterTrace.DCPhase(R.negate()),
	// new CounterTrace.DCPhase(P.and(R.negate())),
	// new CounterTrace.DCPhase()
	// });
	// ctA = compiler.compile("TAbsenceBefore", ct); ctA.dump();
	// return ctA;
	// }

	public PhaseEventAutomata bndResp_Glob(final String id, final CDD P, final CDD S, final int bound) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata mctA;
		final CounterTrace ct =
				new CounterTrace(new CounterTrace.DCPhase[] { phaseTrue(), new CounterTrace.DCPhase(P.and(S.negate())),
						new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, bound), phaseTrue() });
		// MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		// mctA = compiler.compile("TBndResp", mct); //mctA.dump();
		ctA = mCompiler.compile(id + "_TBndResp" + mNameIndex, ct);
		mNameIndex++;
		return ctA;
		// return mctA;
	}

	private static CounterTrace counterTrace(final CounterTrace.DCPhase... phases) {
		if (phases == null || phases.length == 0) {
			throw new IllegalArgumentException("Need at least one phase");
		}
		return new CounterTrace(phases);
	}

	private static DCPhase phase(final CDD x) {
		return new CounterTrace.DCPhase(x);
	}

	private static DCPhase phaseTrue() {
		return new CounterTrace.DCPhase();
	}

}
