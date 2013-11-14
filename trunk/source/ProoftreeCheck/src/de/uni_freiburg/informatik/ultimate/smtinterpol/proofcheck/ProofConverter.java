package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is the front-end for converting an SMTInterpol proof to an
 * Isabelle proof.
 * 
 * @author Christian Schilling
 */
class ProofConverter extends NonRecursive {
	// result stack
	private final ArrayDeque<Term> m_resultStack;
	// appendable
	private final Appendable m_appendable;
	// true iff only the partial proof is given
	private final boolean m_partialProof;
	// term converter
	private final TermConverter m_converter;
	// theory
	private final Theory m_theory;
	// let handler
	private final LetHandler m_letHandler;
	// computation simplifier
	private final ComputationSimplifier m_simplifier;
	// converters
	private final ResolutionConverter m_resConverter;
	private final LemmaCCConverter m_lemmaCCConverter;
	private final LemmaLAConverter m_lemmaLAConverter;
	private final LemmaTrichotomyConverter m_lemmaTrichotomyConverter;
	private final SubstitutionConverter m_substConverter;
	private final SplitConverter m_splitConverter;
	private final TautologyConverter m_tautologyConverter;
	private final RewriteConverter m_rewriteConverter;
	// map for fast proof node conversion
	private final HashMap<String, IProofNode> m_proofNode2Method;
	// map for assertions
	private HashMap<Term, Integer> m_assertion2index;
	// prefix lemmata use
	private static final String LET_LEMMA_PREFIX = "lemma";
	// keywords for special rules
	protected static final String G_ONLY_SUBSTITUTE = "substitute, no print";
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param prettyOutput true iff output file is printed in more convenient
	 *                     human-readable way
	 * @param converter term converter
	 * @param fastProofs true iff fast proofs shall be printed
	 * @param partialProof true iff only the partial proof is given
	 * @param lemmaAppendable appendable for the lemmata
	 */
	public ProofConverter(final Appendable appendable, final Theory theory,
			final boolean prettyOutput, final TermConverter converter,
			final boolean fastProofs, final boolean partialProof,
			final Appendable lemmaAppendable) {
		m_appendable = appendable;
		m_theory = theory;
		m_partialProof = partialProof;
		m_resultStack = new ArrayDeque<Term>();
		m_converter = converter;
		m_letHandler = new LetHandler();
		m_simplifier = new ComputationSimplifier();
		m_resConverter = new ResolutionConverter(appendable, theory,
				converter, m_simplifier, fastProofs,
				lemmaAppendable);
		m_lemmaCCConverter = new LemmaCCConverter(appendable, theory,
				converter, m_simplifier, fastProofs);
		m_lemmaLAConverter = new LemmaLAConverter(appendable, theory,
				converter, m_simplifier, fastProofs,
				lemmaAppendable);
		m_lemmaTrichotomyConverter = new LemmaTrichotomyConverter(appendable,
				theory, converter, m_simplifier);
		m_substConverter = new SubstitutionConverter(appendable, theory,
				converter, m_simplifier);
		m_splitConverter = new SplitConverter(appendable, theory,
				converter, m_simplifier);
		m_tautologyConverter = new TautologyConverter(appendable, theory,
				converter, m_simplifier);
		m_rewriteConverter = new RewriteConverter(appendable, theory,
				converter, m_simplifier, lemmaAppendable);
		
		if (m_partialProof) {
			m_proofNode2Method = new HashMap<String, IProofNode>(
					(int)(4 / 0.75) + 1);
		}
		else {
			m_proofNode2Method = new HashMap<String, IProofNode>(
					(int)(7 / 0.75) + 1);
		}
		fillMap();
	}
	
	/**
	 * This method fills the proof node map with the proof node converters.
	 * For each proof node a conversion object is added to a hash map, which
	 * handles the conversion individually.
	 * 
	 * NOTE: @rewrite and @intern only occur within @eq and have special
	 *       treatment there.
	 */
	private void fillMap() {
		m_proofNode2Method.put("@res", new ResNode());
		m_proofNode2Method.put("@lemma", new LemmaNode());
		m_proofNode2Method.put("@asserted", new AssertedNode());
		m_proofNode2Method.put("@tautology", new TautologyNode());
		if (! m_partialProof) {
			m_proofNode2Method.put("@eq", new EqNode());
			m_proofNode2Method.put("@split", new SplitNode());
			m_proofNode2Method.put("@clause", new ClauseNode());
		}
	}
	
	// [start] general proof conversion //
	
	/**
	 * This method converts the SMTInterpol proof to an Isabelle proof.
	 * 
	 * The proof is pushed on a stack and then iteratively split up to its
	 * sub-terms, based on the {@link NonRecursive} and
	 * {@link de.uni_freiburg.informatik.ultimate.logic.NonRecursive.Walker}
	 * classes.
	 * 
	 * The proof is abbreviated using let expressions (see
	 * {@link ProofWalker#walk(NonRecursive converter, LetTerm term)} for
	 * details).
	 * 
	 * @param proof the proof passed by the solver
	 * @param assertion2index map from assertions to index
	 */
	public void convert(Term proof,
			final HashMap<Term, Integer> assertion2index) {
		m_assertion2index = assertion2index;
		m_resultStack.clear();
		m_letHandler.clear();
		m_converter.switchProofMode();
		
		proof = new FormulaLet(
					new FormulaLet.LetFilter() {
						@Override
						public boolean isLettable(Term term) {
							return ((term instanceof ApplicationTerm) &&
									((ApplicationTerm)term).getFunction().
									getReturnSort().getName() == "@Proof");
						}
					}).let(proof);
		
		writeString("proof -\n");
				
		// start conversion
		enqueueWalker(new ProofWalker(proof, null));
		run();
		
		assert ((m_resultStack.size() == 1) &&
				(m_resultStack.getFirst() == m_theory.FALSE))
				: "The proof must result in 'false'.";
		
		writeString("thus ?thesis by assumption\nqed\n");
		
		// reset converter to checker mode
		m_converter.switchProofMode();
	}
	
	/**
	 * This walker appends a given string to the output when it is taken from
	 * the stack.
	 */
	private class StringWalker implements NonRecursive.Walker {
		// string object
		private final String m_string;
		
		/**
		 * @param string the string to be appended
		 */
		public StringWalker(String string) {
			m_string = string;
		}
		
		@Override
		public void walk(NonRecursive converter) {
			writeString(m_string);
		}
	}
	
	/**
	 * This walker is used for binding a lemma for scoped sub-proofs
	 * (resolution and substitution). The Isabelle translation adds a pair
	 * of scoping parentheses and hence the binding of the last result cannot
	 * be used later on. The solution is to bind the lemma immediately after
	 * the parentheses without remarkable effort.
	 */
	private class ScopingLemmaWalker implements NonRecursive.Walker {
		// string object
		private final TermVariable m_lemmaVar;
		
		/**
		 * @param lemmaVar term variable of lemma binding if any, else null
		 */
		public ScopingLemmaWalker(TermVariable lemmaVar) {
			m_lemmaVar = lemmaVar;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			writeString("note ");
			writeString(LET_LEMMA_PREFIX);
			writeString(m_letHandler.getNumberString(m_lemmaVar));
			writeString(" = this\n");
		}
	}
	
	/**
	 * This walker handles the term conversion on the stack.
	 * It discriminates between the term's sub-type. The only possible terms
	 * are application terms starting with an '@' (proof nodes) and let
	 * bindings/variables, which again only abbreviate those application terms
	 * (see {@link #walk(NonRecursive converter, LetTerm term)} for details).
	 * 
	 * NOTE: All conversion outputs are in reversed order due to stack usage.
	 */
	private class ProofWalker extends NonRecursive.TermWalker {
		// TermVariable of lemma binding if any, else null
		private TermVariable m_lemma;
		
		/**
		 * @param term the term to be converted next
		 * @param lemma TermVariable of lemma binding if any, else null
		 */
		ProofWalker(Term term, TermVariable lemma) {
			super(term);
			m_lemma = lemma;
		}
		
		/**
		 * A constant term is not expected in a proof. The reason is that the
		 * proof is only unfolded until a fixed level (proof nodes), whereas
		 * the base terms are converted using the {@link TermConverter}.
		 */
		@Override
		public void walk(NonRecursive converter, ConstantTerm term) {
			throw new IllegalArgumentException(
					"ConstantTerm is not supported at this level!");
		}
		
		/**
		 * An annotated term is not expected in a proof. They only occur inside
		 * the proof nodes and so are handled there.
		 */
		@Override
		public void walk(NonRecursive converter, AnnotatedTerm term) {
			throw new IllegalArgumentException(
					"AnnotatedTerm is not supported at this level!");
		}
		
		/**
		 * <quantifiers>
		 * This method has to be implemented when quantifiers can be handled. 
		 */
		@Override
		public void walk(NonRecursive converter, QuantifiedFormula term) {
			throw new UnsupportedOperationException(
					"Quantifiers are currently not supported.");
		}
		
		/**
		 * This method converts an application term (proof node). Internally it
		 * just calls the specific sub-method. The following proof nodes are
		 * supported:
		 * 
		 * - @res (resolution)
		 * - @lemma (lemma, both CC and LA)
		 * - @asserted (assertion from input, normalized in partial proof)
		 * - @tautology (tautology)
		 * - @eq (substitution, including equalities @rewrite and @intern)
		 * - @split (split from a disjunction)
		 * - @clause (clause flattening)
		 * 
		 * NOTE: @rewrite and @intern only occur within @eq and have special
		 *       treatment there.
		 * 
		 * @param converter non-recursive converter
		 * @param term application term
		 */
		@Override
		public void walk(NonRecursive converter, ApplicationTerm term) {
			final String name = term.getFunction().getName();
			final Term[] parameters = term.getParameters();
			
			assert (m_proofNode2Method.get(name) != null);
			m_proofNode2Method.get(name).convert(
					converter, parameters, m_lemma);
		}
		
		// [start] let term conversion //
		
		/**
		 * This method converts a let term. A let term is a mapping from term
		 * variables (abbreviations) to terms and a scoped sub-term where the
		 * mapping holds. Each abbreviation is considered iteratively.
		 * 
		 * To avoid proving sub-proofs that occur more than once for several
		 * times, they are collected by the {@link FormulaLet} and abbreviated.
		 * If a let is found, the sub-proof is pushed to the stack here and
		 * later the result is remembered and associated with the variable
		 * instead of the whole proof. After the result has been computed a
		 * {@link #walk(NonRecursive converter, LetTerm term).LetWalker}
		 * observes it and does the variable binding.
		 * 
		 * The translation to Isabelle really treats the abbreviation as a
		 * lemma and so the result of the sub-proof gets an associated name.
		 * Isabelle then only has to look up the proven lemma in the own
		 * variable collection if it occurs later on.
		 * 
		 * @param converter non-recursive converter
		 * @param term let term
		 */
		@Override
		public void walk(NonRecursive converter, LetTerm term) {
			/**
			 * This Walker handles let terms. Only a proof node
			 * (ApplicationTerm starting with an '@') is regarded as a lemma
			 * by the {@link LetFilter} and hence abbreviated.
			 * 
			 * See {@link #walk(NonRecursive converter, LetTerm term)} for more
			 * details.
			 */
			class LetWalker implements NonRecursive.Walker {
				// term variable
				private final TermVariable m_variable;
				
				/**
				 * @param variable the term variable the lemma shall be
				 *        assigned to
				 */
				public LetWalker(TermVariable variable) {
					m_variable = variable;
				}
				
				/**
				 * The last element on the result stack is assigned to the
				 * lemma name.
				 */
				@Override
				public void walk(NonRecursive converter) {
					assert (! m_resultStack.isEmpty());
					final Term lemma = m_resultStack.pop();
					assert (lemma != null);
					m_letHandler.add(m_variable, lemma);
				}
			}
			
			/**
			 * This walker internally translates an equality proof node for
			 * later substitution. Some rewrites are never used and hence are
			 * not translated. To have the rule annotation present in later
			 * substitution steps, the whole proof node is stored for these
			 * cases.
			 */
			class EqualityWalker implements NonRecursive.Walker {
				// rewrite node
				private final ApplicationTerm m_node;
				// true iff node is @rewrite, false iff node is @intern
				private final boolean m_isRewrite;
				// TermVariable of lemma binding if any, else null
				private final TermVariable m_lemmaVar;
				
				/**
				 * @param node rewrite node
				 * @param isRewrite true = @rewrite, false = @intern
				 * @param eqLemmaVar term variable of lemma binding, else null
				 */
				public EqualityWalker(final ApplicationTerm node,
						final boolean isRewrite,
						final TermVariable eqLemmaVar) {
					m_node = node;
					m_isRewrite = isRewrite;
					m_lemmaVar = eqLemmaVar;
				}
				
				@Override
				public void walk(NonRecursive engine) {
					final String proof;
					if (m_isRewrite) {
						proof = convertRewrite(m_node.getParameters());
					}
					else {
						proof = convertIntern(m_node.getParameters());
					}
					
					// the equality was pushed to the result stack
					assert ((m_resultStack.size() > 0) &&
							(m_resultStack.getFirst() instanceof
									ApplicationTerm));
					final ApplicationTerm equality =
							(ApplicationTerm)m_resultStack.pop();
					
					// some proofs should not be translated
					if (proof != G_ONLY_SUBSTITUTE) {
						startSubProof(false, m_lemmaVar);
						m_converter.convert(equality);
						writeString("\" by ");
						writeString(proof);
						
						if (m_isRewrite) {
							m_rewriteConverter.writeLemma();
						}
					}
					else if (m_isRewrite) {
						m_rewriteConverter.forgetLemma();
					}
					
					// memorize result
					m_resultStack.push(m_node);
				}
			}
			
			converter.enqueueWalker(new ProofWalker(term.getSubTerm(),
					m_lemma));
			
			final TermVariable[] variables = term.getVariables();
			final Term[] values = term.getValues();
			assert (variables.length == values.length);
			
			for (int i = variables.length - 1; i >= 0; --i) {
				TermVariable variable = variables[i];
				converter.enqueueWalker(new LetWalker(variable));
				
				// only proof nodes are abbreviated
				if (values[i] instanceof ApplicationTerm) {
					final ApplicationTerm aValue =
							(ApplicationTerm)values[i];
					final String name = aValue.getFunction().getName();
					
					// special handling of equality proof nodes
					if (name == "@rewrite") {
						converter.enqueueWalker(
								new EqualityWalker(aValue, true, variable));
					}
					else if (name == "@intern") {
						converter.enqueueWalker(
								new EqualityWalker(aValue, false, variable));
					}
					else {
						converter.enqueueWalker(new ProofWalker(aValue,
								variable));
					}
				}
				else {
					assert (values[i] instanceof LetTerm);
					converter.enqueueWalker(new ProofWalker(values[i],
							variable));
				}
			}
		}
		
		/**
		 * This method recalls lemmata that have already been proven. This
		 * avoids reproving the same theorem for several times and can only
		 * occur wherever a proof node is expected, e.g., in a resolution or
		 * substitution node.
		 * 
		 * <quantifiers>
		 * This method might have to be modified when quantifiers can be
		 * handled.
		 * 
		 * @param converter non-recursive converter
		 * @param variable term variable
		 */
		public void walk(NonRecursive converter, TermVariable variable) {
			final Term lemma = m_letHandler.getLemma(variable);
			assert (lemma != null);
			
			m_resultStack.push(lemma);
			
			writeString("note ");
			writeString(LET_LEMMA_PREFIX);
			writeString(m_letHandler.getNumberString(variable));
			writeString("\n");
		}
		
		// [end] let term conversion //
	}
	
	// [end] general proof conversion //
	
	// [start] proof node conversion //
	
	/**
	 * This method converts a rewrite proof node (@rewrite).
	 * That is, a trivial equality later used to rewrite a term.
	 * 
	 * The result is received by the substitution converter. It is a string
	 * with the rule's proof if the rule should be translated and a special
	 * keyword if the rule should be ignored. The reason why it is not directly
	 * written to the output is that there exist rewrite rules that are
	 * duplicate and hence can be ignored. This is detected by the substitution
	 * converter, which then decides if the rule should be written or not.
	 * 
	 * The equality is pushed to the result stack nevertheless and the
	 * substitution converter pops it again to run the substitution.
	 * 
	 * @param parameters rewrite parameters
	 * @return string with proof iff rewrite rule was translated, else null
	 */
	private String convertRewrite(Term[] parameters) {
		assert ((parameters.length == 1) &&
				(parameters[0] instanceof AnnotatedTerm));
		final AnnotatedTerm rewrite = (AnnotatedTerm)parameters[0];
		assert (rewrite.getAnnotations().length == 1);
		final String annotation = (String)rewrite.getAnnotations()[0].getKey();
		assert ((rewrite.getSubterm() instanceof ApplicationTerm) &&
				(((ApplicationTerm)rewrite.getSubterm()).getFunction().
						getName() == "=") &&
				(((ApplicationTerm)rewrite.getSubterm()).getParameters().length
						== 2));
		final ApplicationTerm equality = (ApplicationTerm)rewrite.getSubterm();
		
		// proof rule
		final String proof = m_rewriteConverter.convert(equality, annotation);
		assert (proof != null);
		
		// memorize result (can be set to 'False')
		m_resultStack.push(equality);
		
		// return the proof as a string (can be a special keyword)
		return proof;
	}
	
	/**
	 * This method converts an internal rewrite proof node (@intern).
	 * 
	 * @param parameters equality parameters
	 * @return the proof string
	 */
	private String convertIntern(Term[] parameters) {
		assert ((parameters.length == 1) &&
				(parameters[0] instanceof ApplicationTerm));
		final ApplicationTerm equality = (ApplicationTerm)parameters[0];
		assert (equality.getFunction().getName() == "=");
		
		// memorize result
		m_resultStack.push(equality);
		
		return "auto\n";
	}
	
	/**
	 * This method is used to insert a lemma binding in sub-proofs.
	 * 
	 * @param continueProof true iff the proof is continued
	 * @param lemmaVar term variable of lemma binding if any, else null
	 */
	private void startSubProof(final boolean continueProof,
			final TermVariable lemmaVar) {
		// lemma binding
		if (lemmaVar != null) {
			final String lemmaNumber = m_letHandler.getNumberString(lemmaVar);
			
			if (continueProof) {
				writeString("hence ");
			}
			else {
				writeString("have ");
			}
			
			writeString(LET_LEMMA_PREFIX);
			writeString(lemmaNumber);
			writeString(": \"");
		}
		// no lemma binding
		else {
			if (continueProof) {
				writeString("hence \"");
			}
			else {
				writeString("have \"");
			}
		}
	}
	
	/**
	 * This interface is implemented by all proof node converters.
	 */
	private interface IProofNode {
		/**
		 * @param converter non-recursive converter
		 * @param parameters parameters of the split
		 * @param lemmaVar term variable of lemma binding if any, else null
		 */
		void convert(NonRecursive converter, Term[] parameters,
				TermVariable lemmaVar);
	}
	
	/**
	 * This class converts a resolution proof node (@res).
	 */
	private class ResNode implements IProofNode {
		/**
		 * This method converts a resolution proof node (@res).
		 * 
		 * {@inheritDoc}
		 */
		public void convert(NonRecursive converter, Term[] parameters,
				TermVariable lemmaVar) {
			/**
			 * This walker handles resolution steps. The resolution in
			 * SMTInterpol has n > 2 arguments and is used as a chained
			 * (binary) rule. The result of the binary application is always
			 * the first parameter of the next one, meaning n-1 applications
			 * per whole resolution term.
			 * 
			 * Since the arguments themselves can be complicated sub-proofs,
			 * they are computed separately by assumption and then simply the
			 * last two results are taken from the result stack. These are
			 * then used to compute the result of the binary resolution rule.
			 */
			class ResolutionWalker implements NonRecursive.Walker {
				// pivot term
				private final Term m_pivot;
				
				/**
				 * @param pivot the pivot term
				 */
				public ResolutionWalker(Term pivot) {
					m_pivot = pivot;
				}
				
				@Override
				public void walk(NonRecursive converter) {
					assert (m_resultStack.size() > 1);
					final Term second = m_resultStack.pop();
					final Term first = m_resultStack.pop();
					
					assert ((first != null) && (second != null) &&
							(m_pivot != null));
					
					// compute resolution result
					writeString("ultimately\nhave \"");
					final Term result =
							m_resConverter.convert(first, second, m_pivot);
					
					// memorize result
					m_resultStack.push(result);
				}
			}
			
			assert (parameters.length > 1);
			
			if (lemmaVar != null) {
				converter.enqueueWalker(new ScopingLemmaWalker(lemmaVar));
			}
			
			converter.enqueueWalker(new StringWalker("}\n"));
			// terms 2..n with pivot annotation
			for (int i = parameters.length - 1; i > 0; --i) {
				assert (parameters[i] instanceof AnnotatedTerm);
				final AnnotatedTerm next = (AnnotatedTerm)parameters[i];
				final Annotation[] annotation = next.getAnnotations();
				assert ((annotation.length == 1) &&
						(annotation[0].getKey() == ":pivot") &&
						(annotation[0].getValue() instanceof Term));
				
				// resolution with pivot
				converter.enqueueWalker(new ResolutionWalker(
						(Term)annotation[0].getValue()));
				// next term
				converter.enqueueWalker(
						new ProofWalker(next.getSubterm(), null));
				// combination keyword in Isabelle
				converter.enqueueWalker(new StringWalker("moreover\n"));
			}
			// first term
			converter.enqueueWalker(new ProofWalker(parameters[0], null));
			writeString("{\n");
		}
	}
	
	/**
	 * This class converts a lemma proof node (@lemma).
	 */
	private class LemmaNode implements IProofNode {
		/**
		 * This method converts a lemma proof node (@lemma).
		 * 
		 * @param converter non-recursive converter
		 * @param parameters lemma parameters
		 * @param lemmaVar term variable of lemma binding if any, else null
		 */
		public void convert(NonRecursive converter, Term[] parameters,
				TermVariable lemmaVar) {
			assert ((parameters.length == 1) &&
					(parameters[0] instanceof AnnotatedTerm));
			final AnnotatedTerm lemma = (AnnotatedTerm)parameters[0];
			assert (lemma.getAnnotations().length == 1);
			final Annotation annotation = lemma.getAnnotations()[0];
			final String key = annotation.getKey();
			final ApplicationTerm result;
			
			// print header with possible lemma binding
			startSubProof(false, lemmaVar);
			
			// CC lemma (result may change due to reordering)
			if (key == ":CC") {
				result = m_lemmaCCConverter.convert(lemma);
			}
			// LA lemma
			else if (key == ":LA") {
				assert (lemma.getSubterm() instanceof ApplicationTerm);
				result = (ApplicationTerm)lemma.getSubterm();
				assert ((result.getFunction() == m_theory.m_Or) &&
						(annotation.getValue() instanceof Object[]));
				m_lemmaLAConverter.convert(result,
						(Object[])annotation.getValue());
			}
			// trichotomy lemma
			else if (key == ":trichotomy") {
				assert (lemma.getSubterm() instanceof ApplicationTerm);
				result = m_lemmaTrichotomyConverter.convert(
						(ApplicationTerm)lemma.getSubterm());
			}
			else {
				throw new IllegalArgumentException(
						"The lemma is not supported.");
			}
			
			// memorize result
			m_resultStack.push(result);
		}
	}
	
	/**
	 * This class converts an assertion proof node (@asserted).
	 */
	private class AssertedNode implements IProofNode {
		/**
		 * This method converts an assertion proof node (@asserted).
		 * 
		 * @param converter non-recursive converter
		 * @param parameters assertion parameters
		 * @param lemmaVar term variable of lemma binding if any, else null
		 */
		public void convert(final NonRecursive converter,
				final Term[] parameters, final TermVariable lemmaVar) {
			assert (parameters.length == 1);
			Term term = parameters[0];
			
			/*
			 * partial proof mode
			 * NOTE: uses auto and adds mod and div definitions
			 */
			if (m_partialProof) {
				assert ((term instanceof AnnotatedTerm) &&
						(((AnnotatedTerm)term).getAnnotations()[0].getKey() ==
						":input"));
				final AnnotatedTerm aTerm = (AnnotatedTerm)term;
				final String name =
						(String)aTerm.getAnnotations()[0].getValue();
				term = ((AnnotatedTerm)term).getSubterm();
				
				startSubProof(false, lemmaVar);
				m_converter.convert(term);
				writeString("\" using ");
				writeString(name);
				writeString(" unfolding SMTmod_def SMTdiv_def by auto\n");
				
				// memorize result without annotation
				m_resultStack.push(term);
			}
			// extended proof mode
			else {
				assert (m_assertion2index.get(term) != null);
				if (lemmaVar == null) {
					writeString("note ");
					writeString(ProofChecker.ASSERTION_PREFIX);
					writeString(Integer.toString(m_assertion2index.get(term)));
					writeString("\n");
				}
				else {
					writeString("note ");
					writeString(LET_LEMMA_PREFIX);
					writeString(m_letHandler.getNumberString(lemmaVar));
					writeString(" = ");
					writeString(ProofChecker.ASSERTION_PREFIX);
					writeString(Integer.toString(m_assertion2index.get(term)));
					writeString("\n");
				}
				
				// memorize result with annotation (will be split away)
				m_resultStack.push(term);
			}
		}
	}
	
	/**
	 * This class converts a tautology proof node (@tautology).
	 */
	private class TautologyNode implements IProofNode {
		/**
		 * This method converts a tautology proof node (@tautology).
		 * 
		 * @param converter non-recursive converter
		 * @param parameters tautology parameters
		 */
		public void convert(NonRecursive converter, Term[] parameters,
				TermVariable lemmaVar) {
			assert ((parameters.length == 1) &&
					(parameters[0] instanceof AnnotatedTerm));
			final AnnotatedTerm tautology = (AnnotatedTerm)parameters[0];
			assert ((tautology.getAnnotations().length == 1) &&
					(tautology.getSubterm() instanceof ApplicationTerm));
			final String annotation = tautology.getAnnotations()[0].getKey();
			final ApplicationTerm result =
					(ApplicationTerm)tautology.getSubterm();
			
			// convert tautology rule
			startSubProof(false, lemmaVar);
			m_tautologyConverter.convert(result, annotation);
			
			// memorize result
			m_resultStack.push(result);
		}
	}
	
	/**
	 * This class converts a substitution proof node (@eq).
	 */
	private class EqNode implements IProofNode {
		/**
		 * This method converts a substitution proof node (@eq).
		 * 
		 * @param converter non-recursive converter
		 * @param parameters substitution parameters
		 * @param lemmaVar term variable of lemma binding if any, else null
		 */
		@Override
		public void convert(NonRecursive converter, Term[] parameters,
				TermVariable lemmaVar) {
			/**
			 * This walker handles substitution steps. The substitution in
			 * SMTInterpol has n > 2 arguments and is used as a chained
			 * (binary) rule. The result of the binary application is always
			 * the first parameter of the next one, meaning n-1 applications
			 * per whole substitution term.
			 * 
			 * Since the arguments themselves can be complicated sub-proofs,
			 * they are computed separately by assumption and then simply the
			 * last two results are taken from the result stack. These are then
			 * used to compute the result of the binary substitution rule.
			 * 
			 * NOTE: Currently, the rewrite steps are immediately available,
			 *       so it would be possible to directly translate all the
			 *       steps directly without using the stack and walkers.
			 *       It was a design decision to still support rewrite rules
			 *       from other sources (e.g., from another sub-proof).
			 */
			class SubstitutionWalker implements NonRecursive.Walker {
				// the equality proof node
				private final Term m_equalityNode;
				
				/**
				 * @param equalityNode proof node that justifies an equality
				 */
				public SubstitutionWalker(Term equalityNode) {
					m_equalityNode = equalityNode;
				}
				
				@Override
				public void walk(NonRecursive converter) {
					// equality proof node
					final ApplicationTerm node;
					// let lemma if term is a TermVariable, else null
					final TermVariable lemma;
					
					/*
					 * The term is an already proven lemma.
					 * Since it can be useless, it is handled similar to a new
					 * proof node.
					 * 
					 * For such equality nodes the lemma is stored differently.
					 * Instead of only the result, the whole proof node is
					 * stored in order to have the rule annotation present.
					 */
					if (m_equalityNode instanceof TermVariable) {
						lemma = (TermVariable)m_equalityNode;
						final Term lemmaTerm = m_letHandler.getLemma(lemma);
						assert ((lemmaTerm != null) &&
								(lemmaTerm instanceof ApplicationTerm));
						node = (ApplicationTerm)lemmaTerm;
					}
					else {
						lemma = null;
						assert (m_equalityNode instanceof ApplicationTerm);
						node = (ApplicationTerm)m_equalityNode;
					}
					
					/*
					 * Here the term is an equality proof node
					 * (@rewrite/@intern). An equality can be useless, but
					 * unfortunately this cannot be predicted. This is why the
					 * substitution is applied first and if no change occurred,
					 * the rule is ignored.
					 */
					
					final String name = node.getFunction().getName();
					final String proof;
					
					// get proof result from equality rule (not written yet)
					if (name == "@rewrite") {
						proof = convertRewrite(node.getParameters());
					}
					else if (name == "@intern") {
						proof = convertIntern(node.getParameters());
					}
					else {
						throw new IllegalArgumentException("The proof node " +
								name + "is not supported.");
					}
					
					// the equality was pushed to the result stack
					assert ((m_resultStack.size() > 0) &&
							(m_resultStack.getFirst() instanceof
									ApplicationTerm));
					final ApplicationTerm equality =
							(ApplicationTerm)m_resultStack.pop();
					
					// apply substitution and see if there was a change
					assert ((equality.getFunction().getName() == "=") &&
							(equality.getParameters().length == 2));
					assert (m_resultStack.size() > 0);
					final Term first = m_resultStack.pop();
					
					// apply substitution
					final Term result =
							m_substConverter.convert(first, equality);
					assert (result != null);
					
					/*
					 * only write the rules if there was a change
					 * and the rule should in general be translated
					 */
					if ((result != first) && (proof != G_ONLY_SUBSTITUTE)) {
						// write equality proof
						writeString("moreover\n");
						
						// new proof node
						if (lemma == null) {
							startSubProof(false, null);
							m_converter.convert(equality);
							writeString("\" by ");
							writeString(proof);
							
							// write stored pattern lemma
							if (name == "@rewrite") {
								m_rewriteConverter.writeLemma();
							}
						}
						// lemma already proven
						else {
							writeString("note ");
							writeString(LET_LEMMA_PREFIX);
							writeString(m_letHandler.getNumberString(lemma));
							writeString("\n");
							
							// forget stored pattern lemma
							if (name == "@rewrite") {
								m_rewriteConverter.forgetLemma();
							}
						}
						
						/*
						 * write substitution proof
						 * 
						 * NOTE: no lemma binding here due to scoping
						 */
						writeString("ultimately\nhave \"");
						m_converter.convert(result);
						// whole term was substituted
						if (result == equality.getParameters()[1]) {
							writeString("\" by (rule HOL.rev_iffD1)\n");
						}
						// only parts of the term were substituted
						else {
							writeString("\" by (rule eq)\n");
						}
					}
					else {
						// forget stored pattern lemma
						if (name == "@rewrite") {
							m_rewriteConverter.forgetLemma();
						}
					}
					
					// memorize result
					m_resultStack.push(result);
				}
			}
			
			assert (parameters.length > 1);
			
			// lemma binding for scoping
			if (lemmaVar != null) {
				converter.enqueueWalker(new ScopingLemmaWalker(lemmaVar));
			}
			
			/*
			 * NOTE: It can happen that no substitution is written in the end.
			 * In this case the output is just '{\n}\n', so the scoping
			 * parentheses are still written. This is hard to avoid.
			 */
			converter.enqueueWalker(new StringWalker("}\n"));
			
			for (int i = parameters.length - 1; i > 0; --i) {
				converter.enqueueWalker(new SubstitutionWalker(parameters[i]));
			}
			converter.enqueueWalker(new ProofWalker(parameters[0], null));
			writeString("{\n");
		}
	}
	
	/**
	 * This class converts a split proof node (@split).
	 */
	private class SplitNode implements IProofNode {
		/**
		 * This method converts a split proof node (@split).
		 * 
		 * @param converter non-recursive converter
		 * @param parameters parameters of the split
		 * @param lemmaVar term variable of lemma binding if any, else null
		 */
		@Override
		public void convert(NonRecursive converter, Term[] parameters,
				TermVariable lemmaVar) {
			/**
			 * This walker handles @split steps.
			 */
			class SplitWalker implements NonRecursive.Walker {
				// result of the split
				private final ApplicationTerm m_result;
				// annotation
				private final String m_annotation;
				// TermVariable of lemma binding if any, else null
				private final TermVariable m_lemmaVar;
				
				/**
				 * @param result the result of the split node
				 * @param annotation the annotation
				 * @param splitLemmaVar term variable of lemma, else null
				 */
				public SplitWalker(ApplicationTerm result, String annotation,
						TermVariable splitLemmaVar) {
					m_result = result;
					m_annotation = annotation;
					m_lemmaVar = splitLemmaVar;
				}
				
				@Override
				public void walk(NonRecursive converter) {
					assert (m_resultStack.getFirst() instanceof
							ApplicationTerm);
					final ApplicationTerm negDisjunction =
							(ApplicationTerm)m_resultStack.pop();
					
					startSubProof(true, m_lemmaVar);
					m_splitConverter.convert(negDisjunction, m_result,
							m_annotation);
					
					// memorize result
					m_resultStack.push(m_result);
				}
			}
			
			assert ((parameters.length == 2) &&
					(parameters[0] instanceof AnnotatedTerm));
			final AnnotatedTerm split = (AnnotatedTerm)parameters[0];
			assert (split.getAnnotations().length == 1);
			final String annotation = split.getAnnotations()[0].getKey();
			Term subterm = split.getSubterm();
			assert (parameters[1] instanceof ApplicationTerm);
			final ApplicationTerm result = (ApplicationTerm)parameters[1];
			
			// catch result
			converter.enqueueWalker(
					new SplitWalker(result, annotation, lemmaVar));
			
			// convert sub-term first
			converter.enqueueWalker(new ProofWalker(subterm, null));
		}
	}
	
	/**
	 * This class converts a clause proof node (@clause).
	 * 
	 * NOTE: This node is a relic in the SMTInterpol proof, so just unpack it.
	 *       Unused code is commented out.
	 */
	private class ClauseNode implements IProofNode {
		/**
		 * This method converts a clause proof node (@clause).
		 * 
		 * @param converter non-recursive converter
		 * @param parameters clause parameters
		 * @param lemmaVar term variable of lemma binding if any, else null
		 */
		@Override
		public void convert(NonRecursive converter, Term[] parameters,
				TermVariable lemmaVar) {
//			class ClauseWalker implements NonRecursive.Walker {
//				final Term m_result;
//				// TermVariable of lemma binding if any, else null
//				final TermVariable m_lemmaVar;
//				
//				/**
//				 * @param result the result of the flattening
//				 */
//				public ClauseWalker(Term result, TermVariable clauseLemmaVar) {
//					m_result = result;
//					m_lemmaVar = clauseLemmaVar;
//				}
//				
//				@Override
//				public void walk(NonRecursive engine) {
//					assert (! m_resultStack.isEmpty());
//					final Term origin = m_resultStack.pop();
//					
//					// convert rule
//					startSubProof(true, m_lemmaVar);
//					m_converter.convert(m_result);
//					writeString("\" by auto (* @clause *)\n");
//					
//					// memorize result
//					m_resultStack.push(m_result);
//				}
//			}
			
			assert (parameters.length == 2);
//			converter.enqueueWalker(new ClauseWalker(parameters[1], lemmaVar));
			
			converter.enqueueWalker(new ProofWalker(parameters[0], lemmaVar));
		}
	}
	
	// [end] proof node conversion //
	
	// [start] output related //
	
	/**
	 * This method writes a string to the appendable.
	 * 
	 * @param string string that needs not use the stack
	 * @throws RuntimeException thrown if an IOException is caught
	 */
	private void writeString(String string) {
		try {
			m_appendable.append(string);
        } catch (IOException e) {
            throw new RuntimeException("Appender throws IOException", e);
        }
	}
	
	// [end] output related //
}