package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This is our internal representation of a Horn clause. A Horn clause consists
 * of
 * <ul>
 * <li> a body with
 *  <ul>
 *   <li> n uninterpreted predicate symbols (n >= 0)
 *   <li> a transition formula
 *  </ul>
 * <li> a head with either
 *  <ul>
 *   <li> an uninterpreted predicate symbol  or
 *   <li> false
 *  </ul>
 * <li> a mapping that assigns each of the argument positions of the uninterpreted predicate a free variable in the
 *   transition formula
 * </ul>
 * <p>
 * This class stores Horn clauses in a certain normal form:
 * <ul>
 *  <li> The arguments of the head predicate are a list of variables, which are determined by the argument position and
 *    the sort of that argument in the head predicate's signature.
 *      E.g. for two head predicates with the same signature, we have the same arguments.
 *      This also means that the arguments of head predicates never repeat (like "(P x x)").
 * </ul>
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornClause implements IRankedLetter {

	private final List<HcPredicateSymbol> mBodyPreds;

	private final List<List<Term>> mBodyPredToArgs;

	/**
	 * Stores for the predicate symbol in the head at every argument position of
	 * the represented atom, which TermVariable in the transition formula
	 * represents that argument in the represented atom.
	 */
	private final List<HcHeadVar> mHeadPredVariables;
	private final HcPredicateSymbol mHeadPredicate;

	private final HcSymbolTable mHornClauseSymbolTable;

	private final Term mFormula;

	private final boolean mHeadIsFalse;

	/**
	 * Variables occurring in the body. We will quantify over these and those occurring in the head.
	 * (this includes "auxVars", i.e., variables occurring in the constraint only.
	 *
	 * EDIT: note that this may also contain HcBodyAuxVars, which at the moment do not inherit form HcBodyVars
	 */
	private final Set<HcVar> mBodyVariables;

	/**
	 * This field allow one (e.g. the creator of this object) to attach comments to this object.
	 */
	private String mComment;

	/**
	 * Constructor for a query/goal clause, i.e., a Horn clause of the form b1 /\ ... /\ bn /\ constraint --> false.
	 * Where b1 .. bn are uninterpreted predicates and constraint is a Term.
	 *
	 * @param script
	 * @param hcSymbolTable
	 * @param constraint
	 * @param bodyPreds
	 * @param bodyPredToArguments
	 */
	public HornClause(final ManagedScript mgdScript, final HcSymbolTable hcSymbolTable, final Term constraint,
			final List<HcPredicateSymbol> bodyPreds, final List<List<Term>> bodyPredToArguments,
			final Set<HcVar> bodyVars
			) {
		this(mgdScript, hcSymbolTable, constraint, null, Collections.emptyList(), bodyPreds, bodyPredToArguments,
				bodyVars, false);
	}

	public HornClause(final ManagedScript mgdScript, final HcSymbolTable hcSymbolTable, final Term constraint,
			final HcPredicateSymbol headPred, final List<HcHeadVar> headVars,
			final List<HcPredicateSymbol> bodyPreds, final List<List<Term>> bodyPredToArguments,
			final Set<HcVar> bodyVars
			) {
		this(mgdScript, hcSymbolTable, constraint, headPred, headVars, bodyPreds, bodyPredToArguments, bodyVars, false);
		assert headPred != null : "use other constructor for '... -> False' case";
	}

	/**
	 * Constructor for a Horn clause of the form b1 /\ ... /\ bn /\ constraint
	 * --> h. Where b1 .. bn, and h, are uninterpreted predicates and constraint
	 * is a Term.
	 *
	 * @param script
	 *            The script that will be used in TreeAutomizer (not the
	 *            HornClauseParserScript)
	 * @param symbolTable
	 * @param constraint
	 * @param headPred
	 * @param headVars
	 * @param bodyPreds
	 * @param bodyPredToArgs
	 * @param dummy
	 *            dummy parameter to allow for an extra constructor
	 */
	private HornClause(final ManagedScript script, final HcSymbolTable symbolTable, final Term constraint,
			final HcPredicateSymbol headPred, final List<HcHeadVar> headVars,
			final List<HcPredicateSymbol> bodyPreds, final List<List<Term>> bodyPredToArgs,
			final Set<HcVar> bodyVars,
			final boolean dummy) {

		mHornClauseSymbolTable = symbolTable;

		mFormula = constraint;

		mHeadIsFalse = headPred == null;
		mHeadPredicate = headPred;
		mHeadPredVariables = mHeadIsFalse ? Collections.emptyList() : Collections.unmodifiableList(headVars);
		mBodyPreds = Collections.unmodifiableList(bodyPreds);
		mBodyPredToArgs = Collections.unmodifiableList(bodyPredToArgs);
		mBodyVariables = Collections.unmodifiableSet(bodyVars);
	}

	public HcPredicateSymbol getHeadPredicate() {
		if (mHeadIsFalse) {
			throw new AssertionError("Check for isHeadFalse() before calling this");
		}
		return mHeadPredicate;
	}

	public boolean isHeadFalse() {
		return mHeadIsFalse;
	}

	public List<HcPredicateSymbol> getBodyPredicates() {
		return mBodyPreds;
	}

	public int getNoBodyPredicates() {
		return mBodyPreds.size();
	}

	public Term getPredArgTermVariable(final int predPos, final int argPos) {
		return mBodyPredToArgs.get(predPos).get(argPos);
	}

	public List<Term> getTermVariablesForPredPos(final int predPos) {
		return mBodyPredToArgs.get(predPos);
	}

	public List<List<Term>> getBodyPredToArgs() {
		return Collections.unmodifiableList(mBodyPredToArgs);
	}

	public List<HcHeadVar> getTermVariablesForHeadPred() {
		return mHeadPredVariables;
	}

	public void setComment(final String comment) {
		mComment = comment;
	}

	public String getComment() {
		return mComment;
	}

	public boolean hasComment() {
		return mComment != null;
	}


	public String debugString() {
		if (mFormula == null) {
			return "unintialized HornClause";
		}

		final boolean allVarsHaveComment = mBodyVariables.stream().allMatch(HcVar::hasComment)
				&& mHeadPredVariables.stream().allMatch(HcVar::hasComment);
		final Map<Term, Term> prettyVariableSubstitution = new HashMap<>();
		if (allVarsHaveComment) {
			for (final HcVar bv : mBodyVariables) {
				prettyVariableSubstitution.put(bv.getTermVariable(),
						mHornClauseSymbolTable.createPrettyTermVariable(bv.getComment(), bv.getSort()));
			}
			for (final HcHeadVar hv : mHeadPredVariables) {
				prettyVariableSubstitution.put(hv.getTermVariable(),
						mHornClauseSymbolTable.createPrettyTermVariable(hv.getComment(), hv.getSort()));
			}
		}


		String body;
		{
			final StringBuilder bodySb = new StringBuilder();
			for (int i = 0; i < mBodyPredToArgs.size(); ++i) {
				bodySb.append(" ");
				bodySb.append(mBodyPreds.get(i));
				bodySb.append(mBodyPredToArgs.get(i).stream()
						.map(t -> new Substitution(mHornClauseSymbolTable.getManagedScript(),
								prettyVariableSubstitution).transform(t))
						.collect(Collectors.toList()));
//				bodySb.append(")");
			}
			body = bodySb.toString();
			if (body.length() > 0) {
				body = "/\\" + body;
			} else {
				body = "true";
			}
		}

		final String head;
		{
			final String headPred = mHeadIsFalse ? "false" : mHeadPredicate.getName() ;
			head = headPred + mHeadPredVariables.stream()
						.map(t -> new Substitution(mHornClauseSymbolTable.getManagedScript(),
								prettyVariableSubstitution).transform(t.getTermVariable()))
						.collect(Collectors.toList());
		}
		return String.format("%s(%s) /\\ (%s) --> %s",
				hasComment() ? (getComment() + "| ") : "" ,
						body,
						new Substitution(mHornClauseSymbolTable.getManagedScript(),
								prettyVariableSubstitution)
						.transform(mFormula).toString(),
						head);
	}

	@Override
	public String toString() {
		return debugString();
	}

	public HcSymbolTable getHornClauseSymbolTable() {
		return mHornClauseSymbolTable;
	}

	@Override
	public int getRank() {
		return mBodyPreds.size();
	}

	public Term getConstraintFormula() {
		return mFormula;
	}

	/**
	 * Retrieve the variables that occur free in the clause body (as an argument in a body predicate and/or in the
	 * constraint). However, exempt the variables that are arguments of the head predicate.
	 * (these variables roughly correspond to the primed variables in a transition formula..)
	 *
	 * @return
	 */
	public Set<HcVar> getBodyVariables() {
		return mBodyVariables;
	}

	/**
	 *
	 * @param mgdScript
	 * @param nameAssertedTerms
	 * @return a complete Horn constraint as it can be asserted in an (assert ..) term in smtlib.
	 */
	public Term constructFormula(final ManagedScript mgdScript, final boolean nameAssertedTerms) {
		final TermTransferrer termTransferrer = new TermTransferrer(mgdScript.getScript());

		final TermVariable[] qVars;
		final List<TermVariable> headVars;
		{
			final List<HcHeadVar> headVarList = getTermVariablesForHeadPred();
			final Set<HcVar> bodyVars = getBodyVariables();
			headVars = headVarList.stream()
					.map(hv -> (TermVariable) termTransferrer.transform(hv.getTermVariable()))
					.collect(Collectors.toList());

			final List<TermVariable> qVarsList = new ArrayList<>();
			qVarsList.addAll(headVars);
			bodyVars.forEach(bv -> qVarsList.add((TermVariable) termTransferrer.transform(bv.getTermVariable())));
			qVars = qVarsList.toArray(new TermVariable[qVarsList.size()]);
		}

		mgdScript.lock(this);

		final Term head = isHeadFalse() ?
				mgdScript.term(this, "false") :
					mgdScript.term(this, getHeadPredicate().getName(), headVars.toArray(new Term[headVars.size()]));

		final Term tail;
		{
			final List<Term> conjuncts = new ArrayList<>();

			// applications of uninterpreted predicates
			for (int bodyPredIndex = 0; bodyPredIndex < getNoBodyPredicates(); bodyPredIndex++) {
				final HcPredicateSymbol bpsym = getBodyPredicates().get(bodyPredIndex);
				final List<Term> args = getBodyPredToArgs().get(bodyPredIndex).stream()
						.map(termTransferrer::transform).collect(Collectors.toList());
				conjuncts.add(mgdScript.term(this, bpsym.getName(), args.toArray(new Term[args.size()])));
			}

			// constraint
			conjuncts.add(termTransferrer.transform(getConstraintFormula()));

			tail = SmtUtils.and(mgdScript.getScript(), conjuncts);
		}

		final Term clause = mgdScript.term(this, "=>", tail, head);

		final Term result;
		if (qVars.length == 0) {
			result = clause;
	 	} else {
	 		result = mgdScript.getScript().quantifier(QuantifiedFormula.FORALL, qVars, clause);
	 	}

		Term resultFinal;
		if (nameAssertedTerms) {
			// TODO: naming is rather hacky, e.g., on a hash collision, only the first term will get a name.
			try {
				final String qos = "t" + hashCode();
				resultFinal = mgdScript.getScript().annotate(result, new Annotation(":named", qos));
			} catch (final SMTLIBException sle) {
				resultFinal = result;
			}
		} else {
			resultFinal = result;
		}

		mgdScript.unlock(this);
		return resultFinal;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mBodyPredToArgs == null) ? 0 : mBodyPredToArgs.hashCode());
		result = prime * result + ((mBodyPreds == null) ? 0 : mBodyPreds.hashCode());
		result = prime * result + ((mFormula == null) ? 0 : mFormula.hashCode());
		result = prime * result + (mHeadIsFalse ? 1231 : 1237);
		result = prime * result + ((mHeadPredicate == null) ? 0 : mHeadPredicate.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final HornClause other = (HornClause) obj;
		if (mBodyPredToArgs == null) {
			if (other.mBodyPredToArgs != null) {
				return false;
			}
		} else if (!mBodyPredToArgs.equals(other.mBodyPredToArgs)) {
			return false;
		}
		if (mBodyPreds == null) {
			if (other.mBodyPreds != null) {
				return false;
			}
		} else if (!mBodyPreds.equals(other.mBodyPreds)) {
			return false;
		}
		if (mFormula == null) {
			if (other.mFormula != null) {
				return false;
			}
		} else if (!mFormula.equals(other.mFormula)) {
			return false;
		}
		if (mHeadIsFalse != other.mHeadIsFalse) {
			return false;
		}
		if (mHeadPredicate == null) {
			if (other.mHeadPredicate != null) {
				return false;
			}
		} else if (!mHeadPredicate.equals(other.mHeadPredicate)) {
			return false;
		}
		return true;
	}
}
