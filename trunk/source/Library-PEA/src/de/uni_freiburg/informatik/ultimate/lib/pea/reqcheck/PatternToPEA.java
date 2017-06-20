package de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEANet;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PEACompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DOTWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverterDOM;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALWriterV4;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAJ2XMLConverter;

/**
 * The class <code>PatternToPEA</code> offers functionality to transform requirements, formalized as instantiated
 * Patterns, via Countertraces (ct) to PEAS.
 *
 *
 * @author Amalinda Oertel April 2010
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
 */

public class PatternToPEA {
	private Trace2PEACompiler mCompiler = null;
	private ILogger mLogger = null;
	private CDD entry = EventDecision.create("S1");
	// CDD entry = CDD.FALSE;
	private CDD exit = EventDecision.create("S2");
	// CDD exit = CDD.TRUE;
	private CDD missing = CDD.TRUE;

	private int nameindex = 0; // this index is needed so that the counters in the peas for the quantitative patterns
	// do not have the same names
	
	public PatternToPEA(ILogger logger){
		mCompiler = new Trace2PEACompiler(logger);
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// AbsencePattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata absencePattern(final CDD P, final CDD Q, final CDD R, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("AbsenceGlob", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TAbsenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TAbsenceUntil", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(
			        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q),
			                new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TAbsenceAfter", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TAbsBet", ct); // ctA.dump();
			return ctA;
		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Universality Pattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata universalityPattern(final CDD P, final CDD Q, final CDD R, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("univG", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        // new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("univB", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("univU", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("univA", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("univBet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Existence Pattern
	// muß noch für 3scopes erweitert werden
	// Scope Globally
	public PhaseEventAutomata existencePattern(final CDD P, final CDD Q, final CDD R, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			System.out.println("Existence-Globally: Hier muß die Methode noch erweitert werden");
			// CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
			// new CounterTrace.DCPhase(P.negate()),
			// new CounterTrace.DCPhase(),
			// new CounterTrace.DCPhase()
			// });
			// ctA = compiler.compile("ExistenceGlob", ct); ctA.dump();
			// return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(
			        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate().and(R.negate())),
			                new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TExistenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			System.out.println("Existence-Until: Hier muß die Methode noch erweitert werden");
		} else if (scope.contains("After")) {
			System.out.println("Existence-After: Hier muß die Methode noch erweitert werden");
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TExistenceBetween", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Bounded Existence Pattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata bndExistencePattern(final CDD P, final CDD Q, final CDD R, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P),
			        new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("BndExistenceGlob", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate())),
			        // new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TBndExistenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TBndExistenceUntil", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P),
			        new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P),
			        new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TBndExistenceAfter", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("TBndExistenceBetween", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Precedence Pattern
	// komplett und validiert
	// Scope Globally
	public PhaseEventAutomata precedencePattern(final CDD P, final CDD Q, final CDD R, final CDD S,
	        final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(S.negate()),
			        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precedenceGlob", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
			        new CounterTrace.DCPhase(R.negate().and(S.negate())), new CounterTrace.DCPhase(P.and(R.negate())),
			        // new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precedenceBefore", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate()).and(S.negate())),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(P.and(R.negate())),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precedenceUntil", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(S.negate())), new CounterTrace.DCPhase(S.negate()),
			        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precedenceAfter", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(S.negate()).and(R.negate())),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precBet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Precedence Chain Pattern 12
	// Scope Globally
	public PhaseEventAutomata precedenceChainPattern12(final CDD P, final CDD Q, final CDD R, final CDD S, final CDD T,
	        final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(
			        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase(S),
			                new CounterTrace.DCPhase(), new CounterTrace.DCPhase(T), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precCh12G", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(
			        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate().and(R.negate())),
			                new CounterTrace.DCPhase(S.and(R.negate()).and(P.negate())),
			                new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(T.and(R.negate())),
			                // new CounterTrace.DCPhase(R.negate()),
			                // new CounterTrace.DCPhase(R),
			                new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precCh12B", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
			        new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precCh12U", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase(Q.and(P.negate())), new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase(S.and(P.negate())), new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(T), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precCh12A", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase(Q.and(P.negate()).and(R.negate())),
			        new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(S.and(P.negate()).and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("precCh12Bet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Precedence Chain Pattern 21
	// Scope Globally
	// Klappt noch gar nicht
	public PhaseEventAutomata precedenceChainPattern21(final CDD P, final CDD Q, final CDD R, final CDD S, final CDD T,
	        final String scope) {
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

			ctA1 = mCompiler.compile("precCh21G", ct1); // ctA1.dump();

			ctA = mCompiler.compile("precCh21G2", ct); // ctA.dump();
			// ctA = (ctA).parallel(ctA1);

			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			System.out.println("not yet provided");
			ctA = mCompiler.compile("precCh12B", ct); // ctA.dump();
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
			System.out.println("not yet provided");
			ctA = mCompiler.compile("precCh12U", ct); // ctA.dump();
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
			System.out.println("not yet provided");
			ctA = mCompiler.compile("precCh12A", ct); // ctA.dump();
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
			System.out.println("not yet provided");
			ctA = mCompiler.compile("precCh12Bet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// Response Chain Pattern 21
	// Scope Globally
	// Klappt noch gar nicht
	public PhaseEventAutomata responseChainPattern21(final CDD P, final CDD Q, final CDD R, final CDD S, final CDD T,
	        final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA1, ctA2, ctA3;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });

			ctA = mCompiler.compile("respCh21G", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(S.and(R.negate()).and(T.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("respCh21B", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("respCh21U", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("respCh21A", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(S.and(R.negate()).and(T.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(T.and(R.negate())), new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("respCh21Bet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	public PhaseEventAutomata responseChainPattern12(final CDD P, final CDD Q, final CDD R, final CDD S, final CDD T,
	        final String requestedLogic) {
		System.out.println("Not yet implemented");
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// minimum Duration Pattern
	// komplett und validiert
	public PhaseEventAutomata minDurationPattern(final CDD P, final CDD Q, final CDD R, final int timebound,
	        final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(
			        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
			                new CounterTrace.DCPhase(P, CounterTrace.BOUND_LESS, timebound),
			                new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase() });

			ctA = mCompiler.compile("minDurG" + nameindex, ct);

			nameindex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R.negate().and(P.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(R.negate().and(P.negate())),
			        // new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("minDurB" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(R.negate().and(P.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("minDurU" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase(P, CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(P.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("minDurA" + nameindex, ct);
			nameindex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(R.negate().and(P.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("minDurBetween" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// maximum Duration Pattern
	// in Entwicklung
	public PhaseEventAutomata maxDurationPattern(final CDD P, final CDD Q, final CDD R, final int timebound,
	        final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		// mit der auskommentierten Zeile sind wir näher an der Semantik von Konrad/Cheng, aber in der Benutzung ist
		// diese Version die einfachere
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        // new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, timebound), new CounterTrace.DCPhase()

			});
			ctA = mCompiler.compile("maxDurG" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R.negate().and(P.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
			        // new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("maxDurB" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(P.negate().and(R.negate())),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
			        // new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("maxDurU" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.negate()),
			        new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, timebound),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("maxDurA" + nameindex, ct);
			nameindex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
			        new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("maxDurBet" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Response Pattern
	// (außer between) validiert
	public PhaseEventAutomata bndResponsePattern(final CDD P, final CDD Q, final CDD R, final CDD S,
	        final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P.and(S.negate())),
			        // new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATEREQUAL, timebound),
			        new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("bndResG" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R.negate().and(P).and(S.negate())),
			        new CounterTrace.DCPhase(S.negate().and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("bndResB" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
			        new CounterTrace.DCPhase(S.negate().and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("bndResU" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(
			        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q),
			                new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P.and(S.negate())),
			                new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATEREQUAL, timebound),
			                new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("bndResA" + nameindex, ct);
			nameindex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
			        new CounterTrace.DCPhase(S.negate().and(R.negate()), CounterTrace.BOUND_GREATEREQUAL, timebound),
			        new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("bndResBet" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// periodic Pattern
	// komplett und validiert
	public PhaseEventAutomata periodicPattern(final CDD P, final CDD Q, final CDD R, final int timebound,
	        final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_GREATER, 10), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("periG" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
			        // new CounterTrace.DCPhase(R.negate()),
			        // new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("periB" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("periU" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("periA" + nameindex, ct);
			nameindex++;
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.negate().and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("periBet" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// response Pattern
	// NICHT komplett und validiert
	public PhaseEventAutomata responsePattern(final CDD P, final CDD Q, final CDD R, final CDD S, final String scope) {
		PhaseEventAutomata ctA;
		if (scope.contains("Globally")) {
			// hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des intervalls gelten
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			System.out.println("Not yet provided");
			ctA = mCompiler.compile("respG", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("respB", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("until")) {
			// hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des intervalls gelten
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(), });
			System.out.println("Not yet provided");
			ctA = mCompiler.compile("respU", ct); // ctA.dump();
			return ctA;
		} else if (scope.contains("After")) {
			// hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des intervalls gelten
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
			System.out.println("Not yet provided");
			ctA = mCompiler.compile("respA", ct);
			// ctA.dump();
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()).and(S.negate())),
			        new CounterTrace.DCPhase(R.negate().and(S.negate())), new CounterTrace.DCPhase(R),
			        new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("respBet", ct); // ctA.dump();
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Entry Condition Pattern
	public PhaseEventAutomata bndEntryConditionPattern(final CDD P, final CDD Q, final CDD R, final CDD S,
	        final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv1" + nameindex, ct); // ctA.dump();
			nameindex++;

			return ctA;
			// return mctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {

			        new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q.and(R.negate())),
			        new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;

			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate()), CounterTrace.BOUND_GREATER, timebound),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
		return ctA;
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// invariant Pattern
	// validiert
	public PhaseEventAutomata invariantPattern(final CDD P, final CDD Q, final CDD R, final CDD S, final String scope) {
		PhaseEventAutomata ctA;
		ctA = absencePattern(P.and(S.negate()), Q, R, scope);
		return ctA;

	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// bounded Invariance Pattern
	// (außer between) validiert
	public PhaseEventAutomata bndInvariancePattern(final CDD P, final CDD Q, final CDD R, final CDD S,
	        final int timebound, final String scope) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata ctA2;
		if (scope.contains("Globally")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(CDD.TRUE, CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv1" + nameindex, ct); // ctA.dump();
			nameindex++;

			return ctA;
			// return mctA;
		} else if (scope.contains("Before")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())),
			        new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("until")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {

			        new CounterTrace.DCPhase(), new CounterTrace.DCPhase(Q.and(R.negate())),
			        new CounterTrace.DCPhase(R.negate()), new CounterTrace.DCPhase(P.and(R.negate())),
			        new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;

			return ctA;
		} else if (scope.contains("After")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q), new CounterTrace.DCPhase(), new CounterTrace.DCPhase(P),
			        new CounterTrace.DCPhase(CDD.TRUE, CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(S.negate()), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;
		} else if (scope.contains("Between")) {
			final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
			        new CounterTrace.DCPhase(Q.and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(P.and(R.negate())),
			        new CounterTrace.DCPhase(R.negate(), CounterTrace.BOUND_LESS, timebound),
			        new CounterTrace.DCPhase(S.negate().and(R.negate())), new CounterTrace.DCPhase(R.negate()),
			        new CounterTrace.DCPhase(R), new CounterTrace.DCPhase() });
			ctA = mCompiler.compile("inv" + nameindex, ct); // ctA.dump();
			nameindex++;
			return ctA;

		}
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("NoKnownScope", ct);
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

	public PhaseEventAutomata bndResp_Glob(final CDD P, final CDD S, final int bound) {
		PhaseEventAutomata ctA;
		final PhaseEventAutomata mctA;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(P.and(S.negate())),
		        new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, bound), new CounterTrace.DCPhase() });
		// MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		// mctA = compiler.compile("TBndResp", mct); //mctA.dump();
		ctA = mCompiler.compile("TBndResp" + nameindex, ct); // ctA.dump();
		nameindex++;
		return ctA;
		// return mctA;
	}

	public PhaseEventAutomata testPrecedenceVac(final CDD P, final CDD S, final CDD R) {
		PhaseEventAutomata ctA;
		final CounterTrace ct = new CounterTrace(
		        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(S.negate().and(R.negate())),
		                new CounterTrace.DCPhase((P.and(R.negate())).or(S.negate().and(R.negate()))),
		                new CounterTrace.DCPhase() });
		ctA = mCompiler.compile("Test", ct); // ctA.dump();
		return ctA;
	}

	public void runTest3() {
		final CDD A = BooleanDecision.create("A");
		final CDD B = BooleanDecision.create("B");
		final CounterTrace ct = new CounterTrace(
		        new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(A, CounterTrace.BOUND_LESS, 1),
		                new CounterTrace.DCPhase(B, CounterTrace.BOUND_LESSEQUAL, 2) });
		MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
		mCompiler.compile("T3", mct).dump();
		mct = new MCTrace(ct, null, exit, missing, true);
		mCompiler.compile("T4", mct).dump();
	}

	public PhaseEventAutomata deadlockCounterexample(final CDD P, final CDD S, final int bound, final int bound2) {
		PhaseEventAutomata ctA, ctA2;
		final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        // new CounterTrace.DCPhase(P.negate()),
		        new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, bound),
		        // new CounterTrace.DCPhase(P.negate()),
		        new CounterTrace.DCPhase() });

		final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] { new CounterTrace.DCPhase(),
		        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_LESSEQUAL, bound2),
		        new CounterTrace.DCPhase(P), new CounterTrace.DCPhase() });

		// CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
		// new CounterTrace.DCPhase(),
		// new CounterTrace.DCPhase(P, CDD.TRUE, CounterTrace.BOUND_GREATER, bound),
		// new CounterTrace.DCPhase(P),
		// new CounterTrace.DCPhase(P.negate(), CounterTrace.BOUND_LESS, bound2),
		// new CounterTrace.DCPhase(P),
		// new CounterTrace.DCPhase()
		// });
		ctA = mCompiler.compile("TCounterEx", ct);
		ctA.dump();
		ctA2 = mCompiler.compile("TCounterEx2", ct2);
		ctA2.dump();
		ctA = ctA.parallel(ctA2);
		ctA.dump();
		return ctA;
	}

	public void run() {
		PhaseEventAutomata ctParallel, ct1A, ct2A, ct3A;
		final CDD P = BooleanDecision.create("P");
		final CDD S = BooleanDecision.create("S");
		final CDD T = BooleanDecision.create("T");
		final CDD R = BooleanDecision.create("R");
		final CDD Q = BooleanDecision.create("Q");

		// Zweimal sich wiedersprechende BoundedInvariance Anforderungen; Der resultierende Automat ist nur für den Fall
		// G(not(P)) erfüllbar;
		// ct1A = bndInvariance(P, S,10);
		// ct2A = bndInvariance(P, S.negate(),10);
		// ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();

		// Zwei sich widersprechende Anforderungen
		// P--> neg(S) gilt für mindestens 11 time units
		// P--> S gilt in höchstens 10 time units
		ct1A = bndInvariancePattern(P, Q, R, S.negate(), 6, "Globally");
		ct2A = bndResponsePattern(P, Q, R, S, 10, "Globally");
		// ct3A = universalityPattern(P,Q,R,"Globally");
		ct3A = deadlockCounterexample(P, S, 3, 10);
		ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();
		// ctParallel.dumpDot();

		ct1A = absencePattern(P, Q, R, "Before");
		// ct1A.dump();

		ct1A = bndEntryConditionPattern(P, Q, R, S, 100, "Globally");
		ct1A.dump();
		final DOTWriter dotwriter = new DOTWriter("D:/Globally.dot", ct1A);// ctParallel
		dotwriter.write();

		ct1A = bndEntryConditionPattern(P, Q, R, S, 100, "After");
		dotwriter.write("D:/After.dot", ct1A);

		ct1A = bndEntryConditionPattern(P, Q, R, S, 100, "until");
		dotwriter.write("D:/Until.dot", ct1A);

		ct1A = bndEntryConditionPattern(P, Q, R, S, 100, "Between");
		dotwriter.write("D:/Between.dot", ct1A);

		ct1A = bndEntryConditionPattern(P, Q, R, S, 100, "Before");
		dotwriter.write("D:/Before.dot", ct1A);

		// ct1A = responseChainPattern21(P,Q,R,S,T,"Between");
		// ct1A = precedenceChainPattern21(P,Q,R,S,T,"Globally");
		// ct1A.dump();

		ct1A = testPrecedenceVac(P, S, R);
		dotwriter.write("C:/vacuous/TestPrecVac.dot", ct1A);

		ct1A = precedencePattern(P, Q, R, S, "Between");
		ct1A.dump();

		final DOTWriter dotwriter2 = new DOTWriter("C:/minDur.dot", ct1A);
		dotwriter2.write();

		final J2UPPAALWriterV4 j2uppaalWriter = new J2UPPAALWriterV4();
		j2uppaalWriter.writePEA2UppaalFile("C:/UppaalWriterV4_neu.xml", ctParallel);

		final J2UPPAALConverter j2uppaalWr = new J2UPPAALConverter();
		j2uppaalWr.writePEA2UppaalFile("C:/UppaalConverter_neu.xml", ctParallel);

		final J2UPPAALConverterDOM j2uppaalDom = new J2UPPAALConverterDOM();
		j2uppaalDom.create("C:/UppaalConverterDOM.xml", ctParallel);

		try {
			final PEAJ2XMLConverter conv = new PEAJ2XMLConverter();

			final ArrayList<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>();
			peaList.add(ctParallel);
			final PEANet peanet = new PEANet();
			peanet.setPeas(peaList);
			conv.convert(peanet, "AmiTest2.xml");
		} catch (final Exception e) {
			e.printStackTrace();
		}

		// CDD BatteryLow = BooleanDecision.create("BatteryLow");
		// CDD TankLow = BooleanDecision.create("TankLow");
		// CDD GeneratorOn = BooleanDecision.create("GeneratorOn");
		// ct1A = bndResp_Glob(BatteryLow, GeneratorOn, 1);
		// ct2A = bndResp_Glob(TankLow, GeneratorOn.negate(), 2);
		// ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();

		// ct1A = minDuration_Glob();
		// ct2A = maxDuration_Glob();
		// ctParallel = ct1A.parallel(ct2A);
		// ctParallel.dump();

		// ct1A = periodic_Glob();
		// runTest2();
		// runTest3();
	}

	public static void main(final String[] param) {
		new PatternToPEA(ILogger.getLogger("")).run();
	}
}
