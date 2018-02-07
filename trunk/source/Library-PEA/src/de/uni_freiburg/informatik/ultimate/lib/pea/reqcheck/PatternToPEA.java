package de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PEACompiler;

/**
 * The class <code>PatternToPEA</code> offers functionality to transform requirements, formalized as instantiated
 * Patterns, via Countertraces (ct) to PEAS.
 *
 *
 * @author Amalinda Oertel April 2010
 *
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
 */

public class PatternToPEA {
	private final Trace2PEACompiler mCompiler;
	private final ILogger mLogger;

	// this index is needed so that the counters in the peas for the quantitative patterns
	// do not have the same names
	private int mNameIndex = 0;

	public PatternToPEA(final ILogger logger) {
		mLogger = logger;
		mCompiler = new Trace2PEACompiler(logger);
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// AbsencePattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata absencePattern(final String id, final CDD P, final CDD Q, final CDD R,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-AbsenceGlob", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TAbsenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TAbsenceUntil", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q),
							new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TAbsenceAfter", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TAbsBet", ct); // ctA.dump();
			return ctA;
		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Universality Pattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata universalityPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-univG", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-univB", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-univU", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-univA", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-univBet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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
			final CounterTrace ct =
					new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate().and(R.negate())),
							new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TExistenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			mLogger.error("Existence-Until: method incomplete");
		} else if (scope.contains("After")) {
			mLogger.error("Existence-After: method incomplete");
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TExistenceBetween", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P),
					new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-BndExistenceGlob", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TBndExistenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TBndExistenceUntil", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P),
					new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P),
					new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TBndExistenceAfter", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-TBndExistenceBetween", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(S.negate()),
					new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precedenceGlob", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
					new CounterTrace.DCPhase(R.negate().and(S.negate())), new CounterTrace.DCPhase(P.and(R.negate())),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precedenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate()).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(P.and(R.negate())),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precedenceUntil", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(S.negate())), new CounterTrace.DCPhase(S.negate()),
					new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precedenceAfter", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(S.negate()).and(R.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precBet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Precedence Chain Pattern 12
	// Scope Globally
	public PhaseEventAutomata precedenceChainPattern12(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final CDD T, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(S),
							new CounterTrace.DCPhase(), new CounterTrace.DCPhase(T), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precCh12G", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct =
					new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate().and(R.negate())),
							new CounterTrace.DCPhase(S.and(R.negate()).and(P.negate())),
							new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(T.and(R.negate())),
							// new CounterTrace.DCPhase(R.negate()),
							// new CounterTrace.DCPhase(R),
							new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precCh12B", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precCh12U", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(Q.and(P.negate())), new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(S.and(P.negate())), new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(T), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precCh12A", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-precCh12Bet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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
					new CounterTrace.DCPhase(S.and(T.negate())), new CounterTrace.DCPhase(T.negate()),
					new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });

			final CounterTrace ct1 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(T.negate()),
					new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });

			// CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] {
			// new CounterTrace.DCPhase(S.and(T.negate())),
			// new CounterTrace.DCPhase(T.negate()),
			// new CounterTrace.DCPhase(P),
			// new CounterTrace.DCPhase()
			// });

			ctA1 = mCompiler.compile(id + "-precCh21G", ct1); // ctA1.dump();

			ctA = mCompiler.compile(id + "-precCh21G2", ct); // ctA.dump();
			// ctA = (ctA).parallel(ctA1);

			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });

			mLogger.error("precedenceChainPattern21 Before: method incomplete");
			ctA = mCompiler.compile(id + "-precCh12B", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
					// new CounterTrace.DCPhase(P.negate()),
					// new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
					// new CounterTrace.DCPhase(P.negate().and(R.negate())),
					// new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(T.and(R.negate())),
					new CounterTrace.DCPhase() });
			mLogger.error("precedenceChainPattern21 Until: method incomplete");
			ctA = mCompiler.compile(id + "-precCh12U", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
					// new CounterTrace.DCPhase(P.negate()),
					// new CounterTrace.DCPhase(Q.and(P.negate())),
					// new CounterTrace.DCPhase(P.negate()),
					// new CounterTrace.DCPhase(S.and(P.negate())),
					// new CounterTrace.DCPhase(),
					// new CounterTrace.DCPhase(T),
					new CounterTrace.DCPhase() });
			mLogger.error("precedenceChainPattern21 After: method incomplete");
			ctA = mCompiler.compile(id + "-precCh12A", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
					// new CounterTrace.DCPhase(P.negate()),
					// new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
					// new CounterTrace.DCPhase(P.negate().and(R.negate())),
					// new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(T.and(R.negate())),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			mLogger.error("precedenceChainPattern21 Between: method incomplete");
			ctA = mCompiler.compile(id + "-precCh12Bet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });

			ctA = mCompiler.compile(id + "-respCh21G", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(S.and(R.negate()).and(T.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-respCh21B", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-respCh21U", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-respCh21A", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(S.and(R.negate()).and(T.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-respCh21Bet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	public PhaseEventAutomata responseChainPattern12(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final CDD T, final String requestedLogic) {
		mLogger.error("responseChainPattern12: method incomplete");
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// minimum Duration Pattern
	// komplett und validiert
	public PhaseEventAutomata minDurationPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
							new CounterTrace.DCPhase(P, CounterTrace.BOUND_LESS, timebound),
							new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase() });

			ctA = mCompiler.compile(id + "-minDurG" + mNameIndex, ct);

			mNameIndex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R.negate().and(P.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(R.negate().and(P.negate())),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-minDurB" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(R.negate().and(P.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-minDurU" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-minDurA" + mNameIndex, ct);
			mNameIndex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(R.negate().and(P.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-minDurBetween" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					// new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, timebound), new CounterTrace.DCPhase()

			});
			ctA = mCompiler.compile(id + "-maxDurG" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R.negate().and(P.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-maxDurB" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(P.negate().and(R.negate())),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					// new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-maxDurU" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, timebound),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-maxDurA" + mNameIndex, ct);
			mNameIndex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-maxDurBet" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Response Pattern
	// (außer between) validiert
	public PhaseEventAutomata bndResponsePattern(final String id, final CDD P, final CDD Q, final CDD R, final CDD S,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P.and(S.negate())),
					// new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATEREQUAL, timebound),
					new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-bndResG" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R.negate().and(P).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-bndResB" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-bndResU" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(
					new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q),
							new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.and(S.negate())),
							new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATEREQUAL, timebound),
							new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-bndResA" + mNameIndex, ct);
			mNameIndex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
					new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-bndResBet" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// periodic Pattern
	// komplett und validiert
	public PhaseEventAutomata periodicPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_GREATER, 10), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-periG" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					// new CounterTrace.DCPhase(R.negate()),
					// new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-periB" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-periU" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-periA" + mNameIndex, ct);
			mNameIndex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-periBet" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// response Pattern
	// NICHT komplett und validiert
	public PhaseEventAutomata responsePattern(final String id, final CDD P, final CDD Q, final CDD R, final CDD S,
			final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			// hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des intervalls gelten
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			mLogger.error("responsePattern globally: method incomplete");
			ctA = mCompiler.compile(id + "-respG", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-respB", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			// hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des intervalls gelten
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), });
			mLogger.error("responsePattern until: method incomplete");
			ctA = mCompiler.compile(id + "-respU", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			// hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des intervalls gelten
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			mLogger.error("responsePattern after: method incomplete");
			ctA = mCompiler.compile(id + "-respA", ct);
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
					new CounterTrace.DCPhase(R.negate().and(S.negate())), new CounterTrace.DCPhase(R),
					new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-respBet", ct);
			// ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Entry Condition Pattern
	public PhaseEventAutomata bndEntryConditionPattern(final String id, final CDD P, final CDD Q, final CDD R,
			final CDD S, final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv1" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;

			return ctA;
			// return mctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {

					new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q.and(R.negate())),
					new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;

			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Invariance Pattern
	// (außer between) validiert
	public PhaseEventAutomata bndInvariancePattern(final String id, final CDD P, final CDD Q, final CDD R, final CDD S,
			final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(CDD.TRUE, CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv1" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;

			return ctA;
			// return mctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())),
					new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {

					new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q.and(R.negate())),
					new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(P.and(R.negate())),
					new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;

			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P),
					new CounterTrace.DCPhase(CDD.TRUE, CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
					new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(P.and(R.negate())),
					new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_LESS, timebound),
					new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(R.negate()),
					new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile(id + "-inv" + mNameIndex, ct); // ctA.dump();
			mNameIndex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile(id + "-NoKnownScope", ct);
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
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
				new CounterTrace.DCPhase(P.and(S.negate())),
				new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, bound), new CounterTrace.DCPhase() });
		// MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		// mctA = compiler.compile("TBndResp", mct); //mctA.dump();
		ctA = mCompiler.compile(id + "-TBndResp" + mNameIndex, ct); // ctA.dump();
		mNameIndex++;
		return ctA;
		// return mctA;
	}

}
