package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class MSODOperations {

	private final MSODFormulaOperations mFormulaOperations;
	private final MSODAutomataOperations mAutomataOperations;

	public MSODOperations(final MSODFormulaOperations formulaOperations,
			final MSODAutomataOperations automataOperations) {

		mFormulaOperations = formulaOperations;
		mAutomataOperations = automataOperations;
	}

	public NestedWordAutomaton<MSODAlphabetSymbol, String> trueAutomaton(final AutomataLibraryServices services) {

		return mFormulaOperations.trueAutomaton(services);
	}

	public NestedWordAutomaton<MSODAlphabetSymbol, String> falseAutomaton(final AutomataLibraryServices services) {

		return mFormulaOperations.falseAutomaton(services);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c) {

		return mFormulaOperations.strictIneqAutomaton(services, x, c);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y, final Rational c) throws AutomataLibraryException {

		return mFormulaOperations.strictIneqAutomaton(services, x, y, c);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c) {

		return mFormulaOperations.strictNegIneqAutomaton(services, x, c);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictSubsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y) {

		return mFormulaOperations.strictSubsetAutomaton(services, x, y);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> subsetAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y) {

		return mFormulaOperations.subsetAutomaton(services, x, y);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c, final Term y) throws AutomataLibraryException {

		return mFormulaOperations.elementAutomaton(services, x, c, y);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String>
			constElementAutomaton(final AutomataLibraryServices services, final Rational c, final Term x) {

		return mFormulaOperations.constElementAutomaton(services, c, x);
	}

	public NestedWordAutomaton<MSODAlphabetSymbol, String> reconstruct(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<MSODAlphabetSymbol> alphabet,
			final boolean isExtended) {

		return mAutomataOperations.reconstruct(services, automaton, alphabet, isExtended);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		return mAutomataOperations.complement(services, automaton);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> union(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		return mAutomataOperations.union(services, automaton1, automaton2);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> intersect(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		return mAutomataOperations.intersect(services, automaton1, automaton2);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> makeStatesFinal(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<String> states)
			throws AutomataLibraryException {

		return mAutomataOperations.makeStatesFinal(services, automaton, states);
	}

	public Map<Term, Term> getResult(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		return mAutomataOperations.getResult(script, services, automaton);
	}

}