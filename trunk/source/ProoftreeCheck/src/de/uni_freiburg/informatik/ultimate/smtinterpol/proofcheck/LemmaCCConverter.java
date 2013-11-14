package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to convert a lemma of equality (congruence closure, CC).
 * 
 * @author Christian Schilling
 */
public class LemmaCCConverter extends AConverter {
	// true iff fast proofs shall be printed
	private final boolean m_fastProofs;
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	public LemmaCCConverter(final Appendable appendable, final Theory theory,
			final TermConverter converter,
			final ComputationSimplifier simplifier, final boolean fastProofs) {
		super (appendable, theory, converter, simplifier);
		m_fastProofs = fastProofs;
	}
	
	/**
	 * This method converts a Congruence Closure (CC) lemma.
	 * 
	 * The structure of a CC lemma is as follows:
	 * big disjunction A | B (length at least 2, order not determined)
	 * 0 or 1 positive equality A: 0 means 'False', else 1 ('diseq')
	 * n or n-1 negated equalities B
	 * 
	 * The validity of the lemma is given by the rule of the excluded middle 
	 * 'A | ~A', where here '~A ==> B', which is equivalent to '~B ==> A'.
	 * Note that B ('b_1 ~= b_2 | ... | b_(k-1) ~= b_k') becomes
	 * ('b_1 = b_2 & ... & b_(k-1) = b_k') when negated.
	 * 
	 * Two cases are possible:
	 * 
	 * 1) A exists. Then first the B literals are taken to the left hand side
	 * (negated). The sub-path information given by SMTInterpol is used to show
	 * the transitivity resulting in 'b_1 = b_k', which is A and hence finishes
	 * the proof.
	 * Sub-paths behave like lemmata which have to be sorted topologically and
	 * then be proven in Isabelle in the correct order.
	 * To find this order, a special data structure is used, see
	 * {@link SubPathInformation}.
	 * 
	 * 2) A is 'False'. Then the transitivity rule applied to the negated
	 * B chain is of the form 'b_1 = b_k', which then is equal to 'False'
	 * according to the theory. The rest is as in case 1.
	 * 
	 * @param lemma CC formula with sub-path information
	 * @return the result (may have been changed)
	 */
	public ApplicationTerm convert(final AnnotatedTerm lemma) {
		// lemma that is proven
		assert (lemma.getSubterm() instanceof ApplicationTerm);
		ApplicationTerm result = (ApplicationTerm)lemma.getSubterm();
		assert (result.getFunction() == m_theory.m_Or);
		
		/*
		 * annotations guiding the proof
		 * first annotation is the positive equality ('diseq', if existent)
		 * then (":subpath", transitivity chain explaining the main path)
		 * then (":subpath", transitivity chain explaining a path)^*
		 */
		final Object[] annotations =
				(Object[])((Annotation)lemma.getAnnotations()[0]).getValue();
		
		/*
		 * check if there is a positive disjunct and find its position
		 * and make sure that it is in the front (used for proof structure)
		 */
		final boolean noDiseq = (annotations.length % 2 == 0);
		assert (annotations.length >= 2);
		
		// there is a positive disjunct, find it (perhaps create a new term)
		if (! noDiseq) {
			assert ((annotations.length >= 3) &&
					(annotations[0] instanceof ApplicationTerm));
			result = sortDiseq(result, (ApplicationTerm)annotations[0]);
		}
		
		// disjuncts
		final Term[] disjuncts = result.getParameters();
		assert (disjuncts.length > 1);
		
		// header
		m_converter.convert(result);
		writeString("\"\nproof - {\n");
		
		final int offset = noDiseq ? 0 : 1;
		final Term[] mainpath = (Term[])annotations[1 + offset];
		
		/*
		 * data structure for finding the path
		 * NOTE: exploits the fact that Java division is rounding down
		 */
		final SubPathInformation[] subpaths =
				new SubPathInformation[annotations.length / 2];
		for (int i = 0, annotIndex = 1 + offset; i < subpaths.length;
				++i, annotIndex += 2) {
			subpaths[i] =
					new SubPathInformation((Term[])annotations[annotIndex], i);
		}
		final SubPathStack lemmaOrder = new SubPathStack(subpaths.length);
		
		/* create hash maps for fast access */
		
		// map from pair of terms to disjunct with their equality
		final HashMap<TermTuple, ApplicationTerm> eq2disjunct =
				new HashMap<TermTuple, ApplicationTerm>(
						(int)((disjuncts.length - offset + 1) / 0.75) + 1);
		for (int i = offset; i < disjuncts.length; ++i) {
			assert (unquote(disjuncts[i]) != null);
			final ApplicationTerm equality = unquote(disjuncts[i]);
			final Term[] equalTerms = equality.getParameters();
			assert (equalTerms.length == 2);
			eq2disjunct.put(new TermTuple(equalTerms[0], equalTerms[1]),
					equality);
		}
		
		// map from pair of terms to sub-path in between
		final HashMap<TermTuple, SubPathInformation> eq2subpath =
				new HashMap<TermTuple, SubPathInformation>(
						(int)((annotations.length / 2) / 0.75) + 1);
		for (int i = 0; i < subpaths.length; ++i) {
			final Term[] subpath = subpaths[i].m_subpath;
			final TermTuple pair =
					new TermTuple(subpath[0], subpath[subpath.length - 1]);
			assert (! eq2subpath.containsKey(pair));
			eq2subpath.put(pair, subpaths[i]);
		}
		
		// construct lemmata for sub-paths
		constructSubpathLemmata(subpaths, eq2subpath, eq2disjunct, lemmaOrder);
		
		// proof of lemmata (in correct order)
		proveLemmata(subpaths, disjuncts.length, mainpath, offset, lemmaOrder);
		
		// finish proof
		writeString("} qed\n");
		
		return result;
	}
	
	/**
	 * This method sorts the disjunction if the diseq is not the first
	 * disjunct.
	 * 
	 * @param disjunction the disjunction
	 * @param diseq the diseq
	 * @return the old disjunction if the diseq is the first disjunct, else a
	 *         new disjunction
	 */
	private ApplicationTerm sortDiseq(final ApplicationTerm disjunction,
			final ApplicationTerm diseq) {
		assert (diseq.getFunction().getName() == "=");
		final Term[] disjuncts = disjunction.getParameters();
		
		for (int i = 0; i < disjuncts.length; ++i) {
			if (disjuncts[i] instanceof AnnotatedTerm) {
				assert (((AnnotatedTerm)disjuncts[i]).getSubterm() == diseq);
				
				/*
				 * the diseq is not the first disjunct
				 * assert this in a new disjunction
				 * (needed for the proof structure)
				 */
				if (i > 0) {
					final Term[] newDisjuncts = new Term[disjuncts.length];
					newDisjuncts[0] = diseq;
					for (int j = 0; j < i; ++j) {
						newDisjuncts[j + 1] = disjuncts[j];
					}
					for (int j = i + 1; j < newDisjuncts.length; ++j) {
						newDisjuncts[j] = disjuncts[j];
					}
					return m_theory.term(m_theory.m_Or, disjuncts);
				}
				else {
					return disjunction;
				}
			}
		}
		
		throw new IllegalArgumentException(
				"The Diseq was not found, but should exist.");
	}
	
	/**
	 * This method sets up the structures to prove the lemmata for the
	 * sub-paths.
	 * 
	 * @param subpaths the sub-paths
	 * @param eq2subpath mapping equality -> sub-path
	 * @param eq2disjunct mapping equality -> equality disjunct
	 * @param lemmaOrder stack
	 */
	private void constructSubpathLemmata(final SubPathInformation[] subpaths,
			final HashMap<TermTuple, SubPathInformation> eq2subpath,
			final HashMap<TermTuple, ApplicationTerm> eq2disjunct,
			final SubPathStack lemmaOrder) {
		// predefined objects (for pointer sharing, more efficient)
		final AssumptionStep assumSym = new AssumptionStep(true);
		final AssumptionStep assumNonsym = new AssumptionStep(false);
		final CongruenceSubstep argsEqual = new CongruenceSubstep(null, false);
		
		// construct lemmata for sub-paths
		final SubPathStack stack =
				new SubPathStack(subpaths[0], subpaths.length);
		while (true) {
			assert (! stack.isEmpty());
			final SubPathInformation current = stack.top();
			
			// current sub-path is finished, so pop it
			if (current.isFinished()) {
				current.finalize();
				stack.pop();
				assert (current.checkCorrectness());
				
				// lemma can be proven with information at hand
				lemmaOrder.push(current);
				
				// last sub-path (= main path) finished
				if (stack.isEmpty()) {
					return;
				}
				
				stack.top().stepCongruence(current.m_equalities);
			}
			// current sub-path goes on
			else {
				// check if equality follows from assumptions
				final Term[] subpath = current.m_subpath;
				final Term firstTerm = subpath[current.m_localIndex];
				final Term secondTerm = subpath[current.m_localIndex + 1];
				TermTuple pair = new TermTuple(firstTerm, secondTerm);
				final ApplicationTerm assumption = eq2disjunct.get(pair);
				
				// assumption
				if (assumption != null) {
					assert ((eq2subpath.get(pair) == null) ||
							((eq2subpath.get(pair).m_steps.length == 1) &&
									((eq2subpath.get(pair).m_steps[0] == null)
									|| (eq2subpath.get(pair).m_steps[0]
											instanceof AssumptionStep))));
					current.stepAssumption(
							assumption,
							(firstTerm != assumption.getParameters()[0]) ?
									assumSym : assumNonsym);
				}
				// no assumption, so must be a congruence
				else {
					assert ((firstTerm instanceof ApplicationTerm) &&
							(secondTerm instanceof ApplicationTerm));
					final ApplicationTerm first = (ApplicationTerm)firstTerm;
					final ApplicationTerm second = (ApplicationTerm)secondTerm;
					
					// find sub-path for next arguments (if they are not equal)
					
					assert ((first.getFunction() == second.getFunction()) &&
							(first.getParameters().length ==
								second.getParameters().length));
					
					final ISubPathStep aStep =
							current.m_steps[current.m_localIndex];
					final CongruenceStep cStep;
					
					// first encounter
					if (aStep == null) {
						cStep = new CongruenceStep(
								first.getParameters().length);
					}
					else {
						assert (aStep instanceof CongruenceStep);
						cStep = (CongruenceStep)aStep;
					}
					
					if (! cStep.isFinished()) {
						final int subindex = cStep.m_index;
						final Term argumentFirst =
								first.getParameters()[subindex];
						final Term argumentSecond =
								second.getParameters()[subindex];
						
						// arguments are equal, so skip them
						if (argumentFirst == argumentSecond) {
							cStep.m_substeps[subindex] = argsEqual;
						}
						else {
							pair = new TermTuple(argumentFirst,
									argumentSecond);
							
							/* find correct sub-path
							 * do not look for assumptions, since the proof
							 * format ensures that there exists a sub-path
							 */
							final SubPathInformation next =
									eq2subpath.get(pair);
							assert (next != null);
							
							final boolean symmetry =
									(next.m_subpath[0] != argumentFirst);
							
							assert ((! symmetry) ||
									(next.m_subpath[0] == argumentSecond));
							
							assert (cStep.m_substeps[subindex] == null);
							cStep.m_substeps[subindex] =
									new CongruenceSubstep(next, symmetry);
							
							// sub-path not visited yet, compute it
							if (! next.isFinished()) {
								stack.push(next);
							}
						}
						
						current.m_steps[current.m_localIndex] = cStep;
					}
					else {
						current.stepCongruence(null);
					}
				}
			}
		}
	}
	
	/**
	 * This method constructs the proof for the lemmata in Isabelle.
	 * 
	 * A fast proof is supported that concatenates each sub-lemma to one
	 * 'by'-proof. The proof is written with pre-built strings that may
	 * change to handle the last comma in the fast proof (it should be a
	 * closing parenthesis instead). This could also be achieved by writing
	 * the proof to a StringBuilder and replace the character.
	 * 
	 * @param subpaths the sub-paths
	 * @param length length of the disjunction
	 * @param mainpath main path
	 * @param offset offset (0 if diseq is missing, else 1)
	 * @param lemmaOrder stack
	 */
	private void proveLemmata(final SubPathInformation[] subpaths,
			final int length, final Term[] mainpath, final int offset,
			final SubPathStack lemmaOrder) {
		// strings for fast and slow proofs
		final String startFast = m_fastProofs ? "by (" : "";
		final String startReset = m_fastProofs ? "" : "apply (";
		final String startNoParReset = m_fastProofs ? "" : "apply ";
		final String startCopy = m_fastProofs ? ",\n" : "apply (";
		final String startNoParCopy = m_fastProofs ? ",\n" : "apply ";
		final String nextLine = m_fastProofs ? "" : ")\n";
		final String nextLineNoPar = m_fastProofs ? "" : "\n";
		
		int index = 1;
		for (final SubPathInformation currentpath : lemmaOrder.m_stack) {
			if (currentpath.isTrivial()) {
				continue;
			}
			
			final Term[] subpath = currentpath.m_subpath;
			
			// reset start string
			String start = startReset;
			String startNoPar = startNoParReset;
			
			// proof of main-path using lemmata
			if (currentpath.m_globalIndex == 0) {
				// start proving the whole CC lemma
				writeString("show ?thesis\n");
				writeString(startFast);
				
				/*
				 * first disjunct is not present, so add the according literal
				 * equivalent to 'False'
				 */
				if (offset == 0) {
					writeString(start);
					writeString("rule cc_false [where p = \"");
					m_converter.convertToAppendable(mainpath[0], m_appendable);
					writeString(" = ");
					m_converter.convertToAppendable(
							mainpath[mainpath.length - 1], m_appendable);
					writeString("\"], ");
					writeString(m_simplifier.getRule());
					writeString(nextLine);
					
					// overwrite start string
					start = startCopy;
				}
				
				// take each negative literal to get a big meta-implication
				if (length - 1 - offset > 0) {
					writeString(start);
					writeString("intro cc_to_asm, rule cc_to_asm_bin");
					writeString(nextLine);
				}
				else {
					assert (length - 1 - offset == 0);

					writeString(start);
					writeString("rule cc_to_asm_bin");
					writeString(nextLine);
				}
				
				// overwrite start string
				start = startCopy;
				startNoPar = startNoParCopy;
			}
			// proof of a lemma
			else {
				writeString("have ");
				writeString(CC_LEMMA_PREFIX);
				writeString(Integer.toString(index));
				if (! currentpath.m_equalities.isEmpty()) {
					writeString(": \"[|");
					String append = "";
					for (ApplicationTerm equality : currentpath.m_equalities) {
						writeString(append);
						append = "; ";
						m_converter.convertToAppendable(equality,
								m_appendable);
					}
					writeString("|] ==> ");
				}
				else {
					writeString(": \"");
				}
				m_converter.convertToAppendable(subpath[0], m_appendable);
				writeString(" = ");
				m_converter.convertToAppendable(
						subpath[subpath.length - 1], m_appendable);
				writeString("\"\n");
				writeString(startFast);
			}
			
			final ISubPathStep[] steps = currentpath.m_steps;
			for (int i = 0; i < steps.length; ++i) {
				final ISubPathStep step = steps[i];
				final Term secondTerm = subpath[i + 1];
				
				// first step is always a transitivity step
				if (i < steps.length - 1) {
					writeString(start);
					writeString("rule HOL.trans [where s = \"");
					m_converter.convertToAppendable(secondTerm, m_appendable);
					writeString("\"]");
					writeString(nextLine);
					
					// overwrite start string
					start = startCopy;
					startNoPar = startNoParCopy;
				}
				
				/* second step is either by assumption or by lemma */
				
				// proof by assumption (possibly symmetric)
				if (step instanceof AssumptionStep) {
					if (((AssumptionStep)step).m_symmetry) {
						writeString(start);
						writeString("erule HOL.sym");
						writeString(nextLine);
					}
					else {
						writeString(startNoPar);
						writeString("assumption");
						writeString(nextLineNoPar);
					}
				}
				else {
					final CongruenceStep cStep = (CongruenceStep)step;
					final CongruenceSubstep[] substeps = cStep.m_substeps;
					
					// make a copy of the function to change single arguments
					assert (secondTerm instanceof ApplicationTerm);
					final FunctionSymbol function =
							((ApplicationTerm)secondTerm).getFunction();
					final Term[] firstParameters =
							((ApplicationTerm)subpath[i]).getParameters();
					final Term[] secondParameters =
							((ApplicationTerm)secondTerm).getParameters();
					final Term[] parameters = Arrays.copyOf(secondParameters,
							secondParameters.length);
					
					// explain change in arguments by transitivity steps
					for (int j = substeps.length - 1; j > 0; --j) {
						// if the arguments are already equal, skip one step
						if (parameters[j] == firstParameters[j]) {
							continue;
						}
						
						// one transitivity step for one argument less
						parameters[j] = firstParameters[j];
						
						final ApplicationTerm tmpF =
								m_theory.term(function, parameters);
						writeString(start);
						writeString("rule HOL.trans [where s = \"");
						m_converter.convertToAppendable(tmpF, m_appendable);
						writeString("\"]");
						writeString(nextLine);
					}
					
					// explain congruence steps
					for (int j = 0; j < substeps.length; ++j) {
						// if the arguments are already equal, skip one step
						if (secondParameters[j] == firstParameters[j]) {
							continue;
						}
						
						writeString(start);
						writeString("rule cc_cong [where x = \"");
						m_converter.convertToAppendable(
								firstParameters[j], m_appendable);
						writeString("\"]");
						writeString(nextLine);
						
						final CongruenceSubstep congruence = substeps[j];
						
						// lemma is trivial, so it was not created
						final SubPathInformation lemmaSubpath =
								congruence.m_subpath;
						if (lemmaSubpath.isTrivial()) {
							/* symmetry can come from both lemma and current,
							 * so in case of both do not use symmetry
							 */
							final boolean symmetry = (congruence.m_symmetry) ^
									(((AssumptionStep)lemmaSubpath.m_steps[0]).
											m_symmetry);
							
							if (symmetry) {
								writeString(start);
								writeString("erule HOL.sym");
								writeString(nextLine);
							}
							else {
								writeString(startNoPar);
								writeString("assumption");
								writeString(nextLineNoPar);
							}
						}
						else {
							writeString(start);
							writeString("drule (");
							writeString(Integer.toString(
									congruence.m_subpath.m_equalities.size()));
							writeString(") ");
							writeString(CC_LEMMA_PREFIX);
							writeString(Integer.toString(
									congruence.m_subpath.m_lemmaNumber));
							if (congruence.m_symmetry) {
								writeString("[symmetric]");
							}
							writeString(nextLine);
						}
					}
				}
			}
			
			/* finish sub-proof */
			
			// replace last comma by a closing parenthesis
			if (m_fastProofs) {
				writeString(")\n");
			}
			else {
				writeString("done\n");
			}
			
			// assign lemma number
			assert (currentpath.m_lemmaNumber == 0);
			currentpath.m_lemmaNumber = index;
			++index;
		}
	}
	
	/**
	 * This method unpacks the term from the negated :quoted literals.
	 * 
	 * @param term the quoted term (must be an AnnotatedTerm)
	 * @return the inner term
	 */
	private ApplicationTerm unquote(Term term) {
		assert ((term instanceof ApplicationTerm) &&
				(((ApplicationTerm)term).getFunction() == m_theory.m_Not) &&
				(((ApplicationTerm)term).getParameters().length == 1) &&
				(((ApplicationTerm)term).getParameters()[0] instanceof
						AnnotatedTerm) &&
				(((AnnotatedTerm)(((ApplicationTerm)term).getParameters()[0])).
						getAnnotations().length == 1) &&
				(((AnnotatedTerm)(((ApplicationTerm)term).getParameters()[0])).
						getAnnotations()[0].getKey() ==
						":quoted") &&
				(((AnnotatedTerm)(((ApplicationTerm)term).getParameters()[0])).
						getSubterm() instanceof
						ApplicationTerm) &&
				(((ApplicationTerm)((AnnotatedTerm)(((ApplicationTerm)term).
						getParameters()[0])).getSubterm()).getFunction().
						getName() == "="));
		return (ApplicationTerm)((AnnotatedTerm)
				(((ApplicationTerm)term).getParameters()[0])).getSubterm();
	}
	
	/**
	 * This class is an unsorted pair of two terms.
	 * It is used for hashing equality terms, since the order can alter.
	 */
	private class TermTuple {
		// first and second term
		final Term m_first, m_second;
		
		/**
		 * @param first first term
		 * @param second second term
		 */
		public TermTuple(final Term first, final Term second) {
			m_first = first;
			m_second = second;
		}
		
		/**
		 * The hash code is just the sum of the single hash codes.
		 * {@inheritDoc}
		 */
		@Override
		public int hashCode() {
			return m_first.hashCode() + m_second.hashCode();
		}
		
		/**
		 * Two objects are equal if they have the same terms (order ignored).
		 * {@inheritDoc}
		 */
		@Override
		public boolean equals(final Object other) {
			assert (other instanceof TermTuple);
			
			final TermTuple tp = (TermTuple)other;
			if (tp.m_first == m_first) {
				return tp.m_second == m_second;
			}
			else if (tp.m_first == m_second) {
				return tp.m_second == m_first;
			}
			return false;
		}
		
		@Override
		public String toString() {
			return "{{" + m_first.toStringDirect() + ", " +
					m_second.toStringDirect() + "}}";
		}
	}
	
	/**
	 * This interface represents a step in a sub-path annotation in the proof
	 * by SMTInterpol. A step can be justified either by an assumption or by
	 * another sub-path, which means by congruence.
	 */
	private interface ISubPathStep {
		/**
		 * A step can be justified either by assumption or by congruence.
		 * 
		 * @return true iff the step is justified by an assumption
		 */
		public boolean isAssumption();
	}
	
	/**
	 * An assumption step justifies an equality of two terms that is given in
	 * the assumptions in Isabelle, which means is given as a disjunct in the
	 * lemma.
	 * 
	 * The object only has to know if symmetry must be used.
	 */
	private class AssumptionStep implements ISubPathStep {
		// symmetry information
		final boolean m_symmetry;
		
		/**
		 * @param symmetry true iff symmetry rule has to be used
		 */
		public AssumptionStep(final boolean symmetry) {
			m_symmetry = symmetry;
		}
		
		/**
		 * @return true
		 */
		@Override
		public boolean isAssumption() {
			return true;
		}
		
		@Override
		public String toString() {
			if (m_symmetry) {
				return "{{A, t}}";
			}
			return "{{A, f}}";
		}
	}
	
	/**
	 * A congruence step justifies an equality of two function terms, where
	 * the function symbols are the same, but at least one argument differs.
	 * Then for each different argument another sub-path information exists,
	 * proving the equality, even if it is trivial from the assumptions.
	 * 
	 * The single argument equalities are given as sub-steps.
	 */
	private class CongruenceStep implements ISubPathStep {
		// sub-steps array
		final CongruenceSubstep[] m_substeps;
		// index in the steps array
		int m_index;
		
		/**
		 * @param size number of arguments
		 */
		public CongruenceStep(final int size) {
			m_substeps = new CongruenceSubstep[size];
			m_index = 0;
		}
		
		/**
		 * @return false
		 */
		@Override
		public boolean isAssumption() {
			return false;
		}
		
		/**
		 * This method tells if the sub-steps are finished.
		 * 
		 * @return true iff every argument equality is justified
		 */
		public boolean isFinished() {
			/*
			 * Equal arguments are judged by a placeholder object,
			 * so no sub-step must be null.
			 */
			return ((m_index == m_substeps.length - 1) &&
					(m_substeps[m_index] != null));
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{{C, ");
			String append = "";
			for (int i = 0; i < m_substeps.length; ++i) {
				builder.append(append);
				append = ", ";
				builder.append("(");
				if (m_substeps[i] == null) {
					builder.append("null");
				}
				else {
					builder.append(m_substeps[i].m_subpath.m_globalIndex);
					builder.append(", ");
					builder.append(m_substeps[i].m_symmetry);
				}
				builder.append(")");
			}
			builder.append("}}");
			
			return builder.toString();
		}
	}
	
	/**
	 * A congruence sub-step justifies a single equality of two arguments.
	 * Due to the fact that each non-trivial equality (no syntactical equality)
	 * is justified by another sub-path, there is no need for recursive
	 * application of steps, but the sub-steps are final.
	 * 
	 * The sub-step has to know the sub-path and if symmetry must be used.
	 */
	private class CongruenceSubstep {
		// sub-path explaining the congruence
		final SubPathInformation m_subpath;
		// symmetry information
		final boolean m_symmetry;
		
		/**
		 * @param subpath sub-path explaining the equality
		 * @param symmetry true iff symmetry rule has to be used
		 */
		public CongruenceSubstep(final SubPathInformation subpath,
				final boolean symmetry) {
			m_subpath = subpath;
			m_symmetry = symmetry;
		}
		
		@Override
		public String toString() {
			return "(" + m_subpath.m_globalIndex + ", " + m_symmetry + ")";
		}
	}
	
	/**
	 * This class is the data structure for CC lemmata.
	 * Each sub-path object from the proof annotation is wrapped into an
	 * object of this class.
	 * 
	 * The additional information is the steps array (see {@link ISubPathStep}
	 * with the current index (reading from left to right), the global index
	 * used to store the objects and a collection of equalities needed for
	 * this sub-path.
	 * 
	 * Equalities are not stored for the main path, since that would be all
	 * equalities and hence just a waste of memory.
	 */
	private class SubPathInformation {
		// sub-path
		final Term[] m_subpath;
		// equalities needed for the proof
		Collection<ApplicationTerm> m_equalities;
		// proof for single steps
		final ISubPathStep[] m_steps;
		// current index in the sub-path
		int m_localIndex;
		// index in the array of sub-paths
		final int m_globalIndex;
		// lemma number assigned to this sub-path
		int m_lemmaNumber;
		
		/**
		 * @param subpath sub-path wrapped
		 * @param index global index used to store this object
		 */
		public SubPathInformation(final Term[] subpath, final int index) {
			m_subpath = subpath;
			m_equalities = (index > 0) ? new HashSet<ApplicationTerm>() : null;
			m_steps = new ISubPathStep[m_subpath.length - 1];
			m_localIndex = 0;
			m_globalIndex = index;
		}
		
		/**
		 * The next step is considered, where the last step was justified by
		 * an assumption.
		 * 
		 * @param equality equality of the assumption (must be remembered)
		 * @param step assumption step (for object sharing, only two existent)
		 */
		public void stepAssumption(final ApplicationTerm equality,
				final AssumptionStep step) {
			// main path does not need to store equalities (would be all)
			if (m_globalIndex > 0) {
				assert (m_equalities instanceof Set);
				m_equalities.add(equality);
			}
			
			m_steps[m_localIndex] = step;
			
			++m_localIndex;
		}
		
		/**
		 * The next step is considered, where the last step was justified by
		 * a congruence. This method is used for both the whole step and
		 * the sub-steps.
		 * 
		 * @param equalities collection of equalities for sub-steps, else null
		 */
		public void stepCongruence(
				final Collection<ApplicationTerm> equalities) {
			// main path does not need to store equalities (would be all)
			if ((equalities != null) && (m_globalIndex > 0)) {
				m_equalities.addAll(equalities);
			}
			
			assert ((m_steps[m_localIndex] instanceof AssumptionStep) ||
					((m_subpath[m_localIndex] instanceof ApplicationTerm) &&
					(((ApplicationTerm)m_subpath[m_localIndex]).
							getParameters().length > 0)));
			
			if (m_steps[m_localIndex] instanceof CongruenceStep) {
				final CongruenceStep currentStep =
						(CongruenceStep)m_steps[m_localIndex];
				if (currentStep.isFinished()) {
					++m_localIndex;
				}
				else {
					++currentStep.m_index;
				}
			}
			else {
				++m_localIndex;
			}
		}
		
		/**
		 * This method tells if the sub-path is finished.
		 * 
		 * @return true iff every step is justified
		 */
		public boolean isFinished() {
			return (m_localIndex == m_subpath.length - 1);
		}
		
		/**
		 * This method is used in the end to make the Isabelle proof shorter.
		 * 
		 * A sub-path that only explains an equality from the assumptions
		 * needs not be given as a lemma, but often occurs due to the fact that
		 * a congruence is always justified by sub-paths.
		 * 
		 * Then instead of using a lemma, the proof directly uses the
		 * assumption.
		 * 
		 * @return true iff the step follows from the assumptions
		 */
		public boolean isTrivial() {
			assert (isFinished());
			return ((m_steps.length == 1) &&
					(m_steps[0] instanceof AssumptionStep)); 
		}
		
		/**
		 * This method finalizes an object. This means the hash set is
		 * copied to an array list to save some memory and have faster
		 * iteration later.
		 */
		public void finalize() {
			if (m_globalIndex > 0) {
				final ArrayList<ApplicationTerm> newEq =
						new ArrayList<ApplicationTerm>(m_equalities.size());
				newEq.addAll(m_equalities);
				m_equalities = newEq;
			}
		}
		
		/**
		 * This method is only used for asserting correct behavior.
		 * 
		 * @return true iff data structure is handled correctly
		 */
		boolean checkCorrectness() {
			for (ISubPathStep step : m_steps) {
				if (step == null) {
					return false;
				}
				else {
					if (step instanceof CongruenceStep) {
						CongruenceStep cStep = (CongruenceStep)step;
						for (CongruenceSubstep substep : cStep.m_substeps) {
							if (substep == null) {
								return false;
							}
						}
					}
				}
			}
			return true;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{subpath ");
			builder.append(m_globalIndex);
			builder.append(", loc ");
			builder.append(m_localIndex);
			builder.append(", eq = ");
			if (m_equalities == null) {
				builder.append("null");
			}
			else {
				builder.append(m_equalities.toString());
			}
			builder.append(", steps = [");
			String append = "";
			for (int i = 0; i < m_steps.length; ++i) {
				builder.append(append);
				append = ", ";
				if (m_steps[i] == null) {
					builder.append("null");
				}
				else {
					builder.append(m_steps[i].toString());
				}
			}
			builder.append("]}");
			
			return builder.toString();
		}
	}
	
	/**
	 * This class represents a stack used by the CC lemma conversion.
	 * 
	 * It is used in two places:
	 * 
	 * 1) The order in which the lemmata are to be introduced in Isabelle
	 * is given by the order on such a stack.
	 * 
	 * 2) The sub-paths are handled in depth-first manner, which needs a stack.
	 */
	private class SubPathStack {
		// stack
		final SubPathInformation[] m_stack;
		// index of the current element
		int m_index;
		
		/**
		 * This constructor is used for storing the order of the lemmata.
		 * 
		 * @param size the size of the stack
		 */
		public SubPathStack(final int size) {
			m_stack = new SubPathInformation[size];
			m_index = -1;
		}
		
		/**
		 * This constructor is used for the sub-path inspection.
		 * 
		 * @param first the main path, stored at the bottom
		 * @param size the size of the stack
		 */
		public SubPathStack(final SubPathInformation first, final int size) {
			m_stack = new SubPathInformation[size];
			m_index = 0;
			m_stack[0] = first;
		}
		
		/**
		 * @return true iff the stack is empty
		 */
		public boolean isEmpty() {
			return m_index < 0;
		}
		
		/**
		 * This method returns the top-most element on the stack without
		 * removing it.
		 * 
		 * @return the top-most element
		 */
		public SubPathInformation top() {
			assert (m_index >= 0 && m_index < m_stack.length);
			return m_stack[m_index];
		}
		
		/**
		 * This method pushes an element on the stack.
		 * 
		 * @param next new element
		 */
		public void push(final SubPathInformation next) {
			assert (m_index + 1 < m_stack.length);
			m_stack[++m_index] = next;
		}
		
		/**
		 * This method removes the top-most element. Since the size of the
		 * stack is constant, the element is not really removed, but only
		 * the index is decremented.
		 */
		public void pop() {
			--m_index;
		}
		
		@Override
		public String toString() {
			return "{{" + m_stack.toString() + ", " + m_index + "}}";
		}
	}
}