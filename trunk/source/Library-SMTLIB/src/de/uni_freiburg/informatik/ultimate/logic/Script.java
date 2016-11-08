/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

/**
 * Basic interface for the interaction with an SMTLIB version 2 compliant
 * solver.  The interface provides all commands of the SMTLIB version 2 standard
 * and some additional commands to create sorts and terms.
 * 
 * Following table summarizes the standard options that should be understood by
 * every implementation and gives their types.
 * 
 * <table summary="Standard Options">
 * <tr><th>Option</th><th>Type</th></tr>
 * <tr><td>:print-success</td><td>Boolean</td></tr>
 * <tr><td>:produce-proofs</td><td>Boolean</td></tr>
 * <tr><td>:produce-assignments</td><td>Boolean</td></tr>
 * <tr><td>:produce-models</td><td>Boolean</td></tr>
 * <tr><td>:regular-output-channel</td><td>String</td></tr>
 * <tr><td>:diagnostic-output-channel</td><td>String</td></tr>
 * <tr><td>:verbosity</td><td>Integer</td></tr>
 * <tr><td>:interactive-mode</td><td>Boolean</td></tr>
 * <tr><td>:random-seed</td><td>BigInteger</td></tr>
 * <tr><td>:timeout</td><td>BigInteger</td></tr>
 * </table>
 * 
 * @author Jochen Hoenicke, Juergen Christ
 */
public interface Script {
	public static final Sort[] EMPTY_SORT_ARRAY = new Sort[0];
	public static final Term[] EMPTY_TERM_ARRAY = new Term[0];
	/**
	 * A lifted three valued Boolean datatype.  Convenience operators for the
	 * interaction with SMT-solvers written in C are given.
	 * @author Juergen Christ
	 */
	public enum LBool {
		UNSAT {
			@Override
			public String toString() {
				return "unsat";
			}
		},
		UNKNOWN {
			@Override
			public String toString() {
				return "unknown";
			}
		},
		SAT {
			@Override
			public String toString() {
				return "sat";
			}
		};
	}
	/**
	 * Set the logic for the solver.  The logic should be the name of one of the
	 * elements in the {@link Logics} enumeration.
	 * @param logic Name of the logic to set.
	 * @throws UnsupportedOperationException If the logic is not supported by
	 *                                       the solver.
	 * @throws SMTLIBException If a logic is already set.
	 */
	public void setLogic(String logic)
		throws UnsupportedOperationException, SMTLIBException;
	/**
	 * Set the logic for the solver.
	 * @param logic Name of the logic to set.
	 * @throws UnsupportedOperationException If the logic is not supported by
	 *                                       the solver.
	 * @throws SMTLIBException If a logic is already set.
	 */
	public void setLogic(Logics logic)
		throws UnsupportedOperationException, SMTLIBException;
	/**
	 * Set an option for the solver.  At least the options described in the
	 * standard should be valid options.
	 * @param opt   Name of the option.  Note that it has to start with
	 *              <pre>:</pre>.
	 * @param value Value for this option.
	 * @throws UnsupportedOperationException If the option is unsupported.
	 * @throws SMTLIBException In case of type errors.
	 */
	public void setOption(String opt, Object value) 
		throws UnsupportedOperationException, SMTLIBException;
	/**
	 * Set some information for the solver.  Note that according to the standard
	 * a solver has to return success, but ignore the info.
	 * @param info  Name of the info.  Note that it has to start with
	 *              <pre>:</pre>.
	 * @param value Value for this info.
	 */
	public void setInfo(String info, Object value);
	/**
	 * Declare a user-defined sort.
	 * @param sort  The name of the new sort.
	 * @param arity The arity of the new sort.
	 * @throws SMTLIBException If no logic is set, the logic does not allow 
	 *                         user-defined sorts, or a sort with this
	 *                         name already exists.
	 */
	public void declareSort(String sort, int arity) throws SMTLIBException;
	/**
	 * Define an alias of a sort.
	 * @param sort       Name of the alias.
	 * @param sortParams Sort parameters.
	 * @param definition Original sort.
	 * @throws SMTLIBException If no logic is set, the logic does not allow 
	 *                         user-defined sorts, or a sort with this
	 *                         name already exists.
	 */
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
		throws SMTLIBException;
	/**
	 * Declare a function symbol.
	 * @param fun        Name of the function symbol.
	 * @param paramSorts Sorts of the parameters.
	 * @param resultSort Sort of the result of an application of this function.
	 * @throws SMTLIBException If the logic is not set, the logic is not an UF 
	 *                         logic but the function takes parameters, or a 
	 *                         function with this name already exists.
	 */
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
		throws SMTLIBException;
	/**
	 * Define an alias of a function symbol.
	 * @param fun        Name of the alias.
	 * @param params     Parameters of the alias.
	 * @param resultSort Return sort of the alias.
	 * @param definition Definition of the function alias.
	 * @throws SMTLIBException If the logic is not set, the logic is not an UF 
	 *                         logic but the function takes parameters, or a 
	 *                         function with this name already exists.
	 */
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException;
	/**
	 * Push some levels onto the assertion stack.
	 * @param levels The number of levels to push.
	 * @throws SMTLIBException If logic is not set.
	 */
	public void push(int levels) throws SMTLIBException;
	/**
	 * Pop some levels from the assertion stack.
	 * @param levels The number of levels to pop.
	 * @throws SMTLIBException If not enough stack levels are available.
	 */
	public void pop(int levels) throws SMTLIBException;
	/**
	 * Assert a Boolean term into the solver.  The solver might return a change
	 * in the state of the logical context.  Compliant solvers do not have to do
	 * a full check here but return {@link LBool#UNKNOWN}.
	 * @param term The Boolean term to assert.
	 * @return Possibly an unsatisfiability detected by the solver.
	 * @throws SMTLIBException If the term is not Boolean or a named term
	 *                         matches an already defined function.
	 */
	public LBool assertTerm(Term term) throws SMTLIBException;
	/**
	 * Check for satisfiability of the current context.
	 * 
	 * Note that this function should return {@link LBool#UNKNOWN} in case of
	 * errors.
	 * @return The result of the check as a lifted Boolean.
	 * @throws SMTLIBException If the logic is not set.
	 */
	public LBool checkSat() throws SMTLIBException;
	/**
	 * Check for satisfiability of the current context under additional
	 * assumptions.
	 * 
	 * Note that this function should return {@link LBool#UNKNOWN} in case of
	 * errors.
	 * @param assumptions Additional assumptions as Boolean constants (nullary
	 *                    ApplicationTerms of sort Bool or their negations).
	 * @return The result of the check as a lifted Boolean.
	 * @throws SMTLIBException If the logic is not set.
	 */
	public LBool checkSatAssuming(Term... assumptions) throws SMTLIBException;
	/**
	 * Get all assertions contained in the assertion stack.  Note that this
	 * command is only available in interactive mode.  To enable interactive
	 * mode, call
	 * {@link #setOption(String, Object) setOption}(":interactive-mode", true).
	 * @return An array of all asserted terms.
	 * @throws SMTLIBException If interactive mode is not enabled.
	 */
	public Term[] getAssertions() throws SMTLIBException;
	/**
	 * Trigger a call to a proof processor.  Note that this command is only
	 * available if proof production is enabled and the last {@link #checkSat()}
	 *  returned {@link LBool#UNSAT}.  To enable proof production, call
	 * {@link #setOption(String, Object) setOption}(":produce-proofs", true).
	 * @return the proof.  This is given as a big smtlib term of the internal
	 * type {@literal @proof}.
	 * @throws SMTLIBException If proof production is not enabled or the solver
	 *                         did not detect unsatisfiability.
	 * @throws UnsupportedOperationException If proof generation is unsupported.
	 */
	public Term getProof()
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Get the unsat core.  Note that this command is only available if unsat
	 * core production is enabled and the last {@link #checkSat()} returned
	 * {@link LBool#UNSAT}.  To enable unsat core production, call
	 * {@link #setOption(String, Object) setOption}(":produce-unsat-cores",
	 * true).
	 * @return An array of terms forming an unsat core.
	 * @throws SMTLIBException If proof production is not enabled or the solver
	 *                         did not detect unsatisfiability.
	 * @throws UnsupportedOperationException If unsat core computation is
	 *                                       unsupported.
	 */
	public Term[] getUnsatCore()
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Get the unsatisfiable assumptions.  Note that this command is only
	 * available if unsat assumption production is enabled and the last
	 * {@link #checkSatAssuming(Term...)} returned
	 * {@link LBool#UNSAT}.  To enable unsat assumption production, call
	 * {@link #setOption(String, Object) setOption}
	 * (":produce-unsat-assumptions", true).
	 * @return An array of terms that correspond to an unsatisfiable subset of
	 *         last assumptions.
	 * @throws SMTLIBException If unsat assumption production is not enabled or
	 *                         the solver did not detect unsatisfiability.
	 * @throws UnsupportedOperationException If unsat assumption computation is
	 *                                       unsupported.
	 */
	public Term[] getUnsatAssumptions()
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Get values for some terms in the model.  Note that this command is only
	 * available if model production is enabled and the last {@link #checkSat()}
	 * did not return {@link LBool#UNSAT}.  To enable model production, call
	 * {@link #setOption(String, Object) setOption}(":produce-models", true).
	 * @param terms an array of terms whose value should be computed.
	 * @return A valuation (mapping from term to value (which is again 
	 * represented by a term) where the keys are the given terms.
	 * @throws SMTLIBException If model production is not enabled or the solver
	 *                         detected unsatisfiability.
	 * @throws UnsupportedOperationException If model computation is
	 *                                       unsupported
	 */
	public Map<Term, Term> getValue(Term[] terms)
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Get values for all named boolean terms in the model.  Note that this
	 * command is only available if assignment production is enabled and the
	 * last {@link #checkSat()} did not return {@link LBool#UNSAT}.  To
	 * enable assignment production, call
	 * {@link #setOption(String, Object) setOption}(":produce-assignments",
	 * true).
	 * @return An {@link Assignments}.
	 * @throws SMTLIBException If assignment production is not enabled, or the
	 *                         solver did not detect unsatisfiability.
	 * @throws UnsupportedOperationException If model computation is
	 *                                       unsupported
	 */
	public Assignments getAssignment()
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Get the value of an option.
	 * @param opt Name of an option.
	 * @return The value of this option.
	 * @throws UnsupportedOperationException If option is unsupported.
	 */
	public Object getOption(String opt) throws UnsupportedOperationException;
	/**
	 * Get information from the solver.  Note that the solver only has to
	 * implement the info values described in the standard.
	 * @param info Name of the info.  Note that it has to start with
	 *             <pre>:</pre>.
	 * @return Value of the option.
	 * @throws UnsupportedOperationException If the info is unsupported.
	 * @throws SMTLIBException If info is <code>:reason-unknown</code> but last
	 *                         check did not return unknown.
	 */
	public Object getInfo(String info)
		throws UnsupportedOperationException, SMTLIBException;
	/**
	 * Exit the solver.
	 */
	public void exit();
	
	/* Term creation */
	/**
	 * Constant representing universal quantification.
	 */
	public static final int FORALL = QuantifiedFormula.FORALL;
	/**
	 * Constant representing existential quantification.
	 */
	public static final int EXISTS = QuantifiedFormula.EXISTS;
	/**
	 * Instantiate an n-ary sort with parameters.
	 * @param sortname Name of the sort.
	 * @param params   Sort parameters.
	 * @return The corresponding sort.
	 * @throws SMTLIBException If and only if the sort does not exist.
	 */
	public Sort sort(String sortname, Sort... params) throws SMTLIBException;
	/**
	 * Instantiate an indexed n-ary sort with parameters.
	 * @param sortname Name of the sort.
	 * @param indices  Sort indices.
	 * @param params   Sort parameters.
	 * @return The corresponding sort.
	 * @throws SMTLIBException If and only if the sort does not exist.
	 */
	public Sort sort(String sortname, BigInteger[] indices, Sort... params)
		throws SMTLIBException;
	/**
	 * Create an array of sort parameters.  These parameters can be used when
	 * defining a sort.  Note that these names cannot be used in the sort
	 * functions since the result does not contain any real sort.  Users have
	 * to save the array and use its components.  The result contains the
	 * variables in the order in which the names are specified in the input. 
	 * @param names The names of the variables
	 * @return An array corresponding to sort variables with the given names.
	 * @throws SMTLIBException If an error occured.
	 */
	public Sort[] sortVariables(String... names) throws SMTLIBException;
	/**
	 * Create an n-ary term by name.  This function should also be used to
	 * construct Boolean terms. I.e., the function names "and", "or", "=&gt;",
	 * "ite", "=", "distinct", or "not" might be used to create formulas. 
	 * @param funcname Name of the function.
	 * @param params   The parameters of the function application.
	 * @return The constructed term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term term(String funcname, Term... params) throws SMTLIBException;
	/**
	 * Create an n-ary term by name, indices and return sort.  This term
	 * constructor can be used to resolve overloaded function symbols, or create
	 * applications of the "as" function.
	 * @param funcname   Name of the function.
	 * @param indices    Indices for the function.
	 * @param returnSort Return sort of the function.
	 * @param params   The parameters of the function application.
	 * @return The constructed term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term term(String funcname, BigInteger[] indices,
			Sort returnSort, Term... params) throws SMTLIBException;
	/**
	 * Create a term variable.
	 * @param varname Name of the variable.
	 * @param sort    Sort of the variable.
	 * @return The term variable.
	 * @throws SMTLIBException If no name or an invalid sort is given.
	 */
	public TermVariable variable(String varname, Sort sort)
		throws SMTLIBException;
	/**
	 * Create a quantified formula.
	 * @param quantor  The quantor flag (one of {@link #EXISTS}, or 
	 *                 {@link #FORALL})
	 * @param vars     The quantified variables.
	 * @param body     The body of the quantified formula.
	 * @param patterns Possible patterns for e-matching (may be
	 *                 <code>null</code>).
	 * @return The quantified formula.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term quantifier(int quantor, TermVariable[] vars, Term body,
			Term[]... patterns) throws SMTLIBException;
	/**
	 * Create a let term.  Note that you have to provide exactly as many
	 * variables as you provide values.
	 * @param vars   Variables bound by a let.
	 * @param values Values for these variables.
	 * @param body   Body of the let term.
	 * @return The let term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term let(TermVariable[] vars, Term[] values, Term body)
		throws SMTLIBException;
	/**
	 * Annotate a term.  This can be used to create named terms.
	 * @param t           Term to annotate.
	 * @param annotations Annotations for this term.
	 * @return The annotated term.
	 * @throws SMTLIBException If the annotation is invalid, or the evaluation
	 *                         of :named produces an error.
	 */
	public Term annotate(Term t, Annotation... annotations)
		throws SMTLIBException;
	/**
	 * Create a numeral term.
	 * @param num String representation of the numeral.
	 * @return A numeral term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term numeral(String num) throws SMTLIBException;
	/**
	 * Create a numeral term.
	 * @param num the numeral as a big integer.
	 * @return A numeral term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term numeral(BigInteger num) throws SMTLIBException;
	/**
	 * Create a decimal term.
	 * @param decimal String representation of the decimal.
	 * @return A decimal term.
	 */
	public Term decimal(String decimal) throws SMTLIBException;
	/**
	 * Create a decimal term.
	 * @param decimal the decimal as a big decimal.
	 * @return A decimal term.
	 */
	public Term decimal(BigDecimal decimal) throws SMTLIBException;
	/**
	 * Create a hexadecimal term.
	 * @param hex String representation of the hexadecimal.
	 * @return A hexadecimal term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term hexadecimal(String hex) throws SMTLIBException;
	/**
	 * Create a binary term.
	 * @param bin String representation of the binary.
	 * @return A binary term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term binary(String bin) throws SMTLIBException;
	/**
	 * Create a string term.
	 * @param str The parsed string with quotes removed.
	 * @return A string term.
	 * @throws SMTLIBException If an error occurred.
	 */
	public Term string(String str) throws SMTLIBException;
	
	/* Non-SMTLIB extensions */
	/**
	 * Return the underlying theory.  This theory is only valid after a call to
	 * setLogic and before a call to restart.
	 * @return The underlying theory
	 */
//	public Theory getTheory();
	/**
	 * Simplify a term.  This returns a term that is under the current
	 * assertions equivalent to the input term.
	 * @param term A (usually Boolean) term to simplify.
	 * @return The simplified term.
	 * @throws SMTLIBException If an error occurred or unsupported.
	 */
	public Term simplify(Term term) throws SMTLIBException;
	/**
	 * Reset the solver completely.  Note that this invalidates all objects
	 * previously returned and unsets the logic.
	 */
	public void reset();
	/**
	 * Resets the assertion stack.  This option will keep the logic and all
	 * globally defined symbols.
	 */
	public void resetAssertions();
	/**
	 * Get interpolants for the partitions.  Note that the arguments to this
	 * call must either be the names of Boolean top-level assertions, or the
	 * conjunction of such names.
	 * @param partition Partitioning of the assertion stack.
	 * @return Interpolants.
	 * @throws SMTLIBException An error occurred.
	 * @throws UnsupportedOperationException If interpolant computation is
	 *                                       unsupported.
	 */
	public Term[] getInterpolants(Term[] partition)
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Compute a sequence of interpolants.  The nesting array describes the
	 * start of the subtree for tree interpolants.  For inductive sequences of
	 * interpolants use a nesting array completely filled with 0.
	 * @param partition      The array of formulas.  This should contain either
	 * 						 top-level names or conjunction of top-level names.
	 * @param startOfSubtree The start of the subtree containing the formula at
	 * 						 this index as root.
	 * @return Tree interpolants respecting the nesting relation.
	 * @throws SMTLIBException An error occurred.
	 * @throws UnsupportedOperationException If interpolant computation is
	 *                                       unsupported.
	 */
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Retrieve a complete model from the solver.  This is an optional (non-
	 * SMTLIB compliant) operation.  This function can only be called when the
	 * previous {@link #checkSat()} returned {@link LBool#SAT} or (optionally)
	 * {@link LBool#UNKNOWN} and no assertion stack command was issued after
	 * this check.
	 * @return A model for the current formula.
	 * @throws SMTLIBException 
	 * 				Model production was not enabled.
	 * @throws UnsupportedOperationException
	 * 				The solver does not support this operation.
	 */
	public Model getModel()
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Perform an AllSAT computation over some important predicates.
	 * @param predicates The important predicates.  Must be Boolean.
	 * @return Iterator over minterms found during iteration.
	 * @throws SMTLIBException If a predicate is non-Boolean.
	 * @throws UnsupportedOperationException If the operation is unsupported.
	 */
	public Iterable<Term[]> checkAllsat(Term[] predicates)
		throws SMTLIBException, UnsupportedOperationException;
	/**
	 * Try to find an equality between <code>x</code> and <code>y</code> that
	 * is implied in the current satisfiable context.  If successful, this
	 * method returns an array of parameters <code>a,b,c</code> such that the
	 * equality <code>a*x = b*y + c</code> is implied by the current context.
	 * Note that the <code>x</code> array and the <code>y</code> array must be
	 * of equal length and of length at least 2.
	 * @param x The different incarnations of the lhs variable.
	 * @param y The different incarnations of the rhs variable.
	 * @return Array of length 3 or array of length 0 if no equality is implied.
	 */
	public Term[] findImpliedEquality(Term[] x, Term[] y);
	/**
	 * Echo a message on the regular output channel of the solver.  Although
	 * this function is not specified in the SMTLIB standard, we do not expect
	 * implementations to throw any exceptions.  Instead, if the command is
	 * unsupported, it should simply be implemented as the identity function.  
	 * @param msg The message to print.
	 * @return The message.
	 */
	public QuotedObject echo(QuotedObject msg);
}
