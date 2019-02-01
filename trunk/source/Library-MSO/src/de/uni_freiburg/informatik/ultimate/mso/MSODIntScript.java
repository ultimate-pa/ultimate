/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;

public class MSODIntScript extends NoopScript {

	private final IUltimateServiceProvider mUltimateServiceProvider;
	private final AutomataLibraryServices mAutomataLibrarayServices;
	public final ILogger mLogger;
	private Term mAssertionTerm;
	private Map<Term, Term> mModel;

	public MSODIntScript(final IUltimateServiceProvider services, final ILogger logger) {
		mUltimateServiceProvider = services;
		mAutomataLibrarayServices = new AutomataLibraryServices(services);
		mLogger = logger;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mAssertionTerm = mAssertionTerm == null ? term : term("and", new Term[] { mAssertionTerm, term });
		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		mLogger.info("INPUT: " + mAssertionTerm.toString());

		try {

			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton = traversePostOrder(mAssertionTerm);

			final IsEmpty<MSODAlphabetSymbol, String> isEmpty = new IsEmpty<>(mAutomataLibrarayServices, automaton);

			if (!isEmpty.getResult()) {
				final NestedRun<MSODAlphabetSymbol, String> run = isEmpty.getNestedRun();
				final NestedWord<MSODAlphabetSymbol> word = run.getWord();

				final Term[] terms = automaton.getAlphabet().iterator().next().getTerms();
				mModel = MSODUtils.parseMSODiffIntToTerm(this, word, terms);

				mLogger.info("RESULT: SAT");
				mLogger.info("MODEL: " + mModel);
				mLogger.info(automatonToString(automaton, Format.ATS));

				return LBool.SAT;
			}

			mLogger.info("RESULT: UNSAT");
			mLogger.info(automatonToString(automaton, Format.ATS));

			return LBool.UNSAT;

		} catch (final Exception e) {
			mLogger.info(e);
		}

		return LBool.UNKNOWN;
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException {
		final Map<Term, Term> values = new HashMap<>();

		if (mModel == null) {
			return values;
		}

		for (final Term term : terms) {
			Term value = mModel.get(term);

			if (value == null) {
				if (SmtSortUtils.isIntSort(term.getSort())) {
					value = SmtUtils.constructIntValue(this, BigInteger.ZERO);
				}

				if (MSODUtils.isSetOfIntSort(term.getSort())) {
					value = MSODUtils.constructSetOfIntValue(this, new HashSet<BigInteger>());
				}
			}
			values.put(term, value);
		}

		return values;
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	/**
	 * Traverses term in post order.
	 *
	 * @throws AutomataLibraryException
	 *             iff π = 4.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> traversePostOrder(final Term term) throws Exception {
		mLogger.info("Traverse term: " + term);

		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;

			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL) {
				return processForall(quantifiedFormula);
			}

			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS) {
				return processExists(quantifiedFormula);
			}
		}

		if (term instanceof ApplicationTerm) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			final String functionSymbol = applicationTerm.getFunction().getName();

			if (functionSymbol.equals("true")) {
				return processTrue();
			}

			if (functionSymbol.equals("false")) {
				return processFalse();
			}

			if (functionSymbol.equals("not")) {
				return processNegation(applicationTerm);
			}

			if (functionSymbol.equals("and")) {
				return processConjunction(applicationTerm);
			}

			if (functionSymbol.equals("or")) {
				return processDisjunction(applicationTerm);
			}

			if (functionSymbol.equals("=>")) {
				return processImplication(applicationTerm);
			}

			if (functionSymbol.equals("strictSubsetInt")) {
				return processStrictSubset(applicationTerm);
			}

			if (functionSymbol.equals("subsetInt")) {
				return processSubset(applicationTerm);
			}

			if (functionSymbol.equals("element")) {
				return processElement(applicationTerm);
			}

			if (functionSymbol.equals("=")) {
				return processEqual(applicationTerm);
			}

			if (functionSymbol.equals(">")) {
				return processGreater(applicationTerm);
			}

			if (functionSymbol.equals(">=")) {
				return processGreaterEqual(applicationTerm);
			}

			if (functionSymbol.equals("<") || functionSymbol.equals("<=")) {
				return processLessOrLessEqual(applicationTerm);
			}
		}

		throw new IllegalArgumentException("Input must be a QuantifiedFormula or an ApplicationTerm.");
	}

	/**
	 * Returns automaton that represents "forall φ". Performs equivalent
	 * transformation to existential quantifier and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processForall(final QuantifiedFormula term)
			throws Exception {

		final Term subformula = SmtUtils.not(this, term.getSubformula());
		final Term exists = SmtUtils.not(this, quantifier(QuantifiedFormula.EXISTS, term.getVariables(), subformula));

		return traversePostOrder(exists);
	}

	/**
	 * Returns automaton that represents "exists φ".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processExists(final QuantifiedFormula term)
			throws Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getSubformula());
		mLogger.info("Construct ∃ φ: " + term);

		final Term[] quantifiedVariables = term.getVariables();
		final Set<MSODAlphabetSymbol> zeros = MSODUtils.allMatchesAlphabet(result.getAlphabet(), false,
				quantifiedVariables);
		final Set<MSODAlphabetSymbol> ones = MSODUtils.allMatchesAlphabet(result.getAlphabet(), true,
				quantifiedVariables);

		final Set<String> additionalFinals = new HashSet<>();
		final Queue<String> states = new LinkedList<>(result.getFinalStates());

		while (!states.isEmpty()) {
			final Set<String> preds = MSODUtils.hierarchicalPredecessorsIncoming(result, states.poll(), zeros);

			for (final String pred : preds) {
				if (!result.isFinal(pred) && additionalFinals.add(pred)) {
					states.add(pred);
				}
			}
		}

		final Set<Term> freeVars = new HashSet<>(result.getAlphabet().iterator().next().getMap().keySet());
		freeVars.removeAll(Arrays.asList(quantifiedVariables));

		Set<MSODAlphabetSymbol> reducedAlphabet;
		reducedAlphabet = MSODUtils.createAlphabet(freeVars.toArray(new Term[0]));
		result = MSODIntAutomatonFactory.reconstruct(mAutomataLibrarayServices, result, reducedAlphabet, false);
		result = makeStatesFinal(result, additionalFinals);

		return result;
	}

	/**
	 * Returns automaton that represents "true".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processTrue() {
		mLogger.info("Construct true");

		return MSODIntAutomatonFactory.trueAutomaton(mAutomataLibrarayServices);
	}

	/**
	 * Returns automaton that represents "false".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processFalse() {
		mLogger.info("Construct false");

		return MSODIntAutomatonFactory.falseAutomaton(mAutomataLibrarayServices);
	}

	/**
	 * Returns automaton that represents "not φ".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Complement} or {@link Intersect} fails.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processNegation(final ApplicationTerm term)
			throws AutomataLibraryException, Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct not φ: " + term);

		result = new Complement<>(mAutomataLibrarayServices, new MSODStringFactory(), result).getResult();
		if (result.getAlphabet().isEmpty()) {
			return result;
		}

		final Set<Term> intVars = new HashSet<>(result.getAlphabet().iterator().next().getMap().keySet());
		intVars.removeIf(o -> !MSODUtils.isIntVariable(o));

		for (final Term intVar : intVars) {
			NestedWordAutomaton<MSODAlphabetSymbol, String> varAutomaton;
			varAutomaton = MSODIntAutomatonFactory.intVariableAutomaton(mAutomataLibrarayServices, intVar);
			varAutomaton = MSODIntAutomatonFactory.reconstruct(mAutomataLibrarayServices, varAutomaton,
					result.getAlphabet(), true);

			result = new Intersect<>(mAutomataLibrarayServices, new MSODStringFactory(), result, varAutomaton)
					.getResult();
		}

		// TODO: Find best place for minimization.
		final INestedWordAutomaton<MSODAlphabetSymbol, String> minimized;
		result = new MinimizeSevpa<>(mAutomataLibrarayServices, new MSODStringFactory(), result).getResult();

		return result;
	}

	/**
	 * Returns automaton that represents "φ and ... and ψ".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Intersect} fails.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processConjunction(final ApplicationTerm term)
			throws AutomataLibraryException, Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct φ and ψ (0): " + term);

		for (int i = 1; i < term.getParameters().length; i++) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> tmp = traversePostOrder(term.getParameters()[i]);
			mLogger.info("Construct φ and ψ (" + i + "): " + term);

			Set<MSODAlphabetSymbol> symbols;
			symbols = MSODUtils.mergeAlphabets(result.getAlphabet(), tmp.getAlphabet());

			result = MSODIntAutomatonFactory.reconstruct(mAutomataLibrarayServices, result, symbols, true);
			tmp = MSODIntAutomatonFactory.reconstruct(mAutomataLibrarayServices, tmp, symbols, true);

			result = new Intersect<>(mAutomataLibrarayServices, new MSODStringFactory(), result, tmp).getResult();
		}

		result = new MinimizeSevpa<>(mAutomataLibrarayServices, new MSODStringFactory(), result).getResult();
		return result;
	}

	/**
	 * Returns automaton that represents "φ or ... or ψ". Performs equivalent
	 * transformation to conjunction and calls {@link #traversePostOrder(Term)} with
	 * the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processDisjunction(final ApplicationTerm term)
			throws Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct φ and ψ (0): " + term);

		for (int i = 1; i < term.getParameters().length; i++) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> tmp = traversePostOrder(term.getParameters()[i]);
			mLogger.info("Construct φ and ψ (" + i + "): " + term);

			Set<MSODAlphabetSymbol> symbols;
			symbols = MSODUtils.mergeAlphabets(result.getAlphabet(), tmp.getAlphabet());

			result = MSODIntAutomatonFactory.reconstruct(mAutomataLibrarayServices, result, symbols, true);
			tmp = MSODIntAutomatonFactory.reconstruct(mAutomataLibrarayServices, tmp, symbols, true);

			result = new Union<>(mAutomataLibrarayServices, new MSODStringFactory(), result, tmp).getResult();
		}

		result = new MinimizeSevpa<>(mAutomataLibrarayServices, new MSODStringFactory(), result).getResult();
		return result;
	}

	/**
	 * Returns automaton that represents "φ implies ψ". Performs equivalent
	 * transformation to "not φ and ψ" and calls {@link #traversePostOrder(Term)}
	 * with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processImplication(final ApplicationTerm term)
			throws Exception {

		final Term[] terms = term.getParameters();
		for (int i = 0; i < terms.length - 1; i++) {
			terms[i] = SmtUtils.not(this, terms[i]);
		}

		return traversePostOrder(SmtUtils.or(this, terms));
	}

	/**
	 * Returns automaton that represents "t = c". Performs equivalent transformation
	 * to "t <= c and not t < c" and calls {@link #traversePostOrder(Term)} with the
	 * result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processEqual(final ApplicationTerm term) throws Exception {

		final Term[] terms = term.getParameters();
		final Term lessEqual = SmtUtils.leq(this, terms[0], terms[1]);
		final Term greaterEqual = SmtUtils.not(this, SmtUtils.less(this, terms[0], terms[1]));
		final Term equal = SmtUtils.and(this, lessEqual, greaterEqual);

		return traversePostOrder(equal);
	}

	/**
	 * Returns automaton that represents "t > c". Performs equivalent transformation
	 * to "not t <= c" and calls {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processGreater(final ApplicationTerm term)
			throws Exception {

		final Term[] terms = term.getParameters();
		final Term greater = SmtUtils.not(this, SmtUtils.leq(this, terms[0], terms[1]));

		return traversePostOrder(greater);
	}

	/**
	 * Returns automaton that represents "t >= c". Performs equivalent
	 * transformation to "not t < c" and calls {@link #traversePostOrder(Term)} with
	 * the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processGreaterEqual(final ApplicationTerm term)
			throws Exception {

		final Term[] terms = term.getParameters();
		final Term greaterEqual = SmtUtils.not(this, SmtUtils.less(this, terms[0], terms[1]));

		return traversePostOrder(greaterEqual);
	}

	/**
	 * Returns automaton that represents "t < c" or "t <= c".
	 *
	 * @throws NotAffineException
	 *             if construction of {@link AffineRelation} fails.
	 * @throws AutomataLibraryException
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processLessOrLessEqual(final ApplicationTerm term)
			throws NotAffineException, AutomataLibraryException {

		final AffineRelation affineRelation = new AffineRelation(this, term, TransformInequality.NONSTRICT2STRICT);
		final AffineTerm affineTerm = affineRelation.getAffineTerm();
		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant().negate();

		if (variables.size() == 1) {
			final Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (var.getValue().equals(Rational.ONE)) {
				mLogger.info("Construct x < c: " + term);
				return MSODIntAutomatonFactory.strictIneqAutomaton(mAutomataLibrarayServices, var.getKey(), constant);
			}

			if (var.getValue().equals(Rational.MONE)) {
				mLogger.info("Construct -x < c: " + term);
				return MSODIntAutomatonFactory.strictNegIneqAutomaton(mAutomataLibrarayServices, var.getKey(),
						constant);
			}
		}

		if (variables.size() == 2) {
			mLogger.info("Construct x-y < c: " + term);

			final Iterator<Entry<Term, Rational>> it = variables.entrySet().iterator();
			final Entry<Term, Rational> var1 = it.next();
			final Entry<Term, Rational> var2 = it.next();

			if (!var1.getValue().add(var2.getValue()).equals(Rational.ZERO)) {
				throw new IllegalArgumentException("Input is not difference logic.");
			}

			if (var1.getValue().equals(Rational.ONE)) {
				return MSODIntAutomatonFactory.strictIneqAutomaton(mAutomataLibrarayServices, var1.getKey(),
						var2.getKey(), constant);
			}

			if (var2.getValue().equals(Rational.ONE)) {
				return MSODIntAutomatonFactory.strictIneqAutomaton(mAutomataLibrarayServices, var2.getKey(),
						var1.getKey(), constant);
			}
		}

		throw new IllegalArgumentException("Invalid inequality");
	}

	/**
	 * Returns automaton that represents "X strictSubset Y".
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> processStrictSubset(final ApplicationTerm term) {
		mLogger.info("Construct X strictSubset Y: " + term);

		if (term.getParameters().length != 2) {
			throw new IllegalArgumentException("StrictSubset must have exactly two parameters.");
		}

		return MSODIntAutomatonFactory.strictSubsetAutomaton(mAutomataLibrarayServices, term.getParameters()[0],
				term.getParameters()[1]);
	}

	/**
	 * Returns automaton that represents "X subset Y".
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> processSubset(final ApplicationTerm term) {
		mLogger.info("Construct X subset Y: " + term);

		if (term.getParameters().length != 2) {
			throw new IllegalArgumentException("Subset must have exactly two parameters.");
		}

		return MSODIntAutomatonFactory.subsetAutomaton(mAutomataLibrarayServices, term.getParameters()[0],
				term.getParameters()[1]);
	}

	/**
	 * Returns automaton that represents "t element X".
	 * 
	 * @throws AutomataLibraryException
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processElement(final ApplicationTerm term)
			throws AutomataLibraryException {
		if (term.getParameters().length != 2) {
			throw new IllegalArgumentException("Element must have exactly two parameters.");
		}

		final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(this).transform(term.getParameters()[0]);

		if (affineTerm.isErrorTerm()) {
			throw new IllegalArgumentException("Could not create AffineTerm.");
		}

		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant();

		if (variables.size() == 0) {
			mLogger.info("Construct c element X: " + term);
			return MSODIntAutomatonFactory.constElementAutomaton(mAutomataLibrarayServices, constant,
					term.getParameters()[1]);
		}

		if (variables.size() == 1) {
			mLogger.info("Construct x+c element Y: " + term);
			final Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (!var.getValue().equals(Rational.ONE)) {
				throw new IllegalArgumentException("Invalid input.");
			}

			return MSODIntAutomatonFactory.elementAutomaton(mAutomataLibrarayServices, var.getKey(), constant,
					term.getParameters()[1]);
		}

		throw new IllegalArgumentException("Invalid input.");
	}

	/**
	 * Returns a automaton where also the given states are final.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if construction of {@link NestedWordAutomatonReachableStates}
	 *             fails.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> makeStatesFinal(
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<String> states)
			throws AutomataOperationCanceledException {

		NestedWordAutomatonReachableStates<MSODAlphabetSymbol, String> nwaReachableStates;
		nwaReachableStates = new NestedWordAutomatonReachableStates<>(mAutomataLibrarayServices, automaton);

		final Set<String> finals = new HashSet<>(automaton.getFinalStates());
		finals.addAll(states);

		return new NestedWordAutomatonFilteredStates<>(mAutomataLibrarayServices, nwaReachableStates,
				automaton.getStates(), automaton.getInitialStates(), finals);
	}

	/**
	 * Checks if the language of the given automaton is empty.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if construction of {@link IsEmpty} fails.
	 */
	private void checkEmptiness(final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataOperationCanceledException {

		final IsEmpty<MSODAlphabetSymbol, String> isEmpty = new IsEmpty<>(mAutomataLibrarayServices, automaton);

		if (!isEmpty.getResult()) {
			final NestedRun<MSODAlphabetSymbol, String> run = isEmpty.getNestedRun();
			final NestedWord<MSODAlphabetSymbol> word = run.getWord();
		}
	}

	/**
	 * Returns a string representation of the given automaton. (only for debugging)
	 */
	private String automatonToString(final IAutomaton<?, ?> automaton, final Format format) {
		AutomatonDefinitionPrinter<?, ?> printer;
		printer = new AutomatonDefinitionPrinter<>(mAutomataLibrarayServices, "", Format.ATS, automaton);

		return printer.getDefinitionAsString();
	}
}
