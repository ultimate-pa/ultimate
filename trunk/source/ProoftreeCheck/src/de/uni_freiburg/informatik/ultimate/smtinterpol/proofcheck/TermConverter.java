package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck.LemmaLAConverter.FactorWrapper;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck.NamedWrapper;

/**
 * Terms in SMT-LIB syntax must be converted to Isabelle syntax before passing
 * them to Isabelle. This is what happens here.
 * 
 * @author Christian Schilling
 */
class TermConverter extends NonRecursive {
	// appendable
	private Appendable m_appendable;
	// printing numeric types
	private boolean m_printTypes;
	// use more convenient output?
	private final boolean m_prettyOutput;
	// map for interpreted functions
	private final HashMap<String, IFunction> m_funTrans;
	// maps for uninterpreted functions to compatible name
	private final HashMap<FunctionSymbol, String> m_function2compFunction;
	// list and stack for :named annotations
	private LinkedList<NamedWrapper> m_namedList;
	private ArrayDeque<NamedWrapper> m_namedStack;
	// lambda and conjunction in parentheses for pretty printing modes
	private final String m_andInPar;
	private final String m_lambda;
	// lambda variable prefix
	private static final String LAMBDA_VAR_PREFIX = "x";
	
	/**
	 * @param appendable appendable to write the term to
	 * @param prettyOutput true iff output file is printed in a more convenient
	 *                     human-readable way
	 */
	public TermConverter(final Appendable appendable, final Logics logics,
			final boolean prettyOutput) {
		m_appendable = appendable;
		m_prettyOutput = prettyOutput;
		m_andInPar = m_prettyOutput ? ") \\<and> (" : ") & (";
		m_printTypes = false;
		m_function2compFunction = new HashMap<FunctionSymbol, String>();
		m_lambda = m_prettyOutput ? "((\\<lambda>" : "((%";
		
		// fill function
		m_funTrans = new HashMap<String, IFunction>((int)(25 / 0.75) + 1);
		fillMap();
	}
	
	// [start] general conversion //
	
	
	
	/**
	 * This method converts an SMT-LIB term to an Isabelle term and
	 * appends it to the internal string memory.
	 * 
	 * The term is pushed on a stack and then iteratively split up to its
	 * sub-terms, based on the {@link NonRecursive} and
	 * {@link de.uni_freiburg.informatik.ultimate.logic.NonRecursive.Walker}
	 * classes.
	 * 
	 * @param term the SMT-LIB term
	 */
	public void convert(final Term term) {
		enqueueWalker(new TermConverterWalker(term));
		run();
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
		public StringWalker(final String string) {
			m_string = string;
		}
		
		@Override
		public void walk(final NonRecursive converter) {
			writeString(m_string);
		}
	}
	
	/**
	 * This walker adds nested :named annotations in the correct order to the
	 * list.
	 */
	private class NamedWalker implements NonRecursive.Walker {
		final int m_stackSize;
		
		public NamedWalker(int stackSize) {
			m_stackSize = stackSize;
		}

		@Override
		public void walk(final NonRecursive converter) {
			if (m_namedStack != null) {
				for (int i = m_namedStack.size() - m_stackSize; i >= 0; --i) {
					assert (! m_namedStack.isEmpty());
					final NamedWrapper wrapper = m_namedStack.pop();
					m_namedList.add(wrapper);
				}
			}
		}
	}
	
	/**
	 * This walker converts a term (in SMT-LIB syntax) to an
	 * Isabelle-compatible format.
	 * 
	 * NOTE: All conversion outputs are in reversed order due to stack usage.
	 * 
	 * @param term the SMT-LIB term
	 */
	private class TermConverterWalker extends NonRecursive.TermWalker {
		/**
		 * @param term the term
		 */
		public TermConverterWalker(final Term term) {
			super(term);
		}
		
		/**
		 * This method converts a constant term.
		 * A constant is always a number.
		 * 
		 * NOTE: the sorts are not always correct, since a numeral
		 * is defined to be of sort Int, but in mixed logics it can be of sort
		 * Real. Isabelle automatically infers type conversion.
		 * 
		 * @param converter non-recursive converter
		 * @param term constant term
		 */
		@Override
		public void walk(final NonRecursive converter,
				final ConstantTerm term) {
			final String termName = term.getSort().getName();
			if (termName == "Int") {
				writeString("(");
				
				enqueueWalker(new StringWalker("::int)"));
				enqueueWalker(new StringWalker(term.toString()));
			}
			else if (termName == "Real") {
				// decimal
				if (term.getValue() instanceof BigDecimal) {
					final BigDecimal number = (BigDecimal)term.getValue();
					final String string = number.toString();
					int scale = number.scale();
					final boolean fraction;
					
					/*
					 * pretty printing drops all unnecessary fractions and
					 * zeroes
					 */
					if (m_prettyOutput) {
						if (scale > 0) {
							int point = string.length() - scale;
							
							int i = point + 1;
							for (; i < string.length(); ++i) {
								if (string.charAt(i) != '0') {
									break;
								}
							}
							if (i == string.length()) {
								fraction = false;
							}
							else {
								fraction = true;
							}
							
							if (fraction) {
								writeString("((");
								// if the integer part is zero, drop it as well
								if (! string.startsWith("0")) {
									assert (point > 2);
									writeString(string.substring(0,
											point - 1));
								}
								writeString(string.substring(i));
							}
							else {
								writeString("(");
								writeString(string.substring(0, point - 1));
							}
						}
						else {
							writeString("(");
							writeString(string);
							fraction = false;
						}
					}
					// only ignore a single decimal zero
					else {
						if (scale > 1) {
							writeString("((");
							int point = string.length() - scale;
							writeString(string.substring(0, point - 1));
							writeString(string.substring(point));
							fraction = true;
						}
						/*
						 * integer-valued reals have the form 'x.0'
						 * this is always ignored
						 */
						else if ((scale == 1) && (string.endsWith("0"))) {
							writeString("(");
							writeString(string.substring(0,
									string.length() - 2));
							fraction = false;
						}
						else {
							writeString("(");
							writeString(string);
							fraction = false;
						}
					}
					

					/*
					 * NOTE: For fractions only one of the numbers must be
					 *       typed as real.
					 */
					writeString("::real");
					
					if (fraction) {
						writeString(") / 1");
						while (--scale >= 0) {
							writeString("0");
						}
					}
					writeString(")");
				}
				// integer, but sort real
				else {
					assert (term.getValue() instanceof BigInteger);
					writeString("(");
					writeString(term.getValue().toString());
					writeString("::real)");
				}
			}
			else {
				throw new IllegalArgumentException(
						"The constant type is not supported.");
			}
		}
		
		/**
		 * This method converts an annotated term.
		 * 
		 * Annotations are completely ignored and only the sub-term is pushed
		 * to the stack.
		 * 
		 * @param converter non-recursive converter
		 * @param term annotated term
		 */
		@Override
		public void walk(final NonRecursive converter,
				final AnnotatedTerm term) {
			final Term subterm = term.getSubterm();
			
			// assertion mode, store :named bindings
			if (m_namedStack != null) {
				final Annotation[] annotations = term.getAnnotations();
				boolean found = false;
				for (int i = 0; i < annotations.length; ++i) {
					final Annotation annot = annotations[i];
					if (annot.getKey().equals(":named")) {
						assert (annot.getValue() instanceof String);
						
						m_namedStack.push(new NamedWrapper(
								((String)annot.getValue()), subterm));
						
						// afterwards take in reverse order from the stack
						if (! found) {
							found = true;
							enqueueWalker(
									new NamedWalker(m_namedStack.size()));
						}
					}
				}
			}
			
			enqueueWalker(new TermConverterWalker(subterm));
		}
		
		/**
		 * This method converts an application term.
		 * 
		 * Internally it is a huge case split for every possible term that
		 * calls the specific handler.
		 * 
		 * It currently works for:
		 * 
		 * Bool functions:
		 * true, false, and, or, =>, not, xor, ite
		 * 
		 * equality functions:
		 * =, distinct
		 * 
		 * LA functions:
		 * <=, <, >=, >, +, - (unary and binary), *, /, mod, div, abs
		 * divisible, to_int, to_real, is_int
		 * 
		 * CC functions:
		 * uninterpreted functions
		 * 
		 * @param converter non-recursive converter
		 * @param term application term
		 */
		@Override
		public void walk(final NonRecursive converter,
				final ApplicationTerm term) {
			final FunctionSymbol function = term.getFunction();
			// intern function
			if (function.isIntern()) {
				m_funTrans.get(function.getName()).convert(term);
			}
			// non-intern function
			else {
				toNoninternFunction(function, term.getParameters());
			}
		}
		
		/**
		 * This method converts a let term.
		 * 
		 * @param converter non-recursive converter
		 * @param term let term
		 */
		@Override
		public void walk(final NonRecursive converter, final LetTerm term) {
			final TermVariable[] variables = term.getVariables();
			final Term[] values = term.getValues();
			
			assert ((values.length == variables.length) &&
					(values.length > 0));
			
			writeString("(let ");
			
			enqueueWalker(new StringWalker(")"));
			enqueueWalker(new TermConverterWalker(term.getSubTerm()));
			enqueueWalker(new StringWalker(" in "));
			for (int i = variables.length - 1; i >= 1; --i) {
				enqueueWalker(new TermConverterWalker(values[i]));
				enqueueWalker(new StringWalker(" = "));
				enqueueWalker(new TermConverterWalker(variables[i]));
				enqueueWalker(new StringWalker("; "));
			}
			enqueueWalker(new TermConverterWalker(values[0]));
			enqueueWalker(new StringWalker(" = "));
			enqueueWalker(new TermConverterWalker(variables[0]));
		}
		
		/**
		 * This method converts a quantified term.
		 * 
		 * Currently not implemented, since SMTInterpol does not support it.
		 * 
		 * <quantifiers>
		 * This method has to be implemented when quantifiers can be handled.
		 * 
		 * @param converter non-recursive converter
		 * @param term quantified term
		 */
		@Override
		public void walk(final NonRecursive converter,
				final QuantifiedFormula term) {
			throw new UnsupportedOperationException(
					"Quantifiers are currently not supported.");
		}
		
		/**
		 * This method converts a term variable.
		 * A term variable is used in 'let' and quantified formulae.
		 * 
		 * <quantifiers>
		 * This method might have to be changed when quantifiers can be
		 * handled.
		 * 
		 * @param converter non-recursive converter
		 * @param term term variable
		 */
		@Override
		public void walk(final NonRecursive converter,
				final TermVariable term) {
			writeString(toCompatibleString(term.getName()));
		}
	}
	
	// [end] general conversion //
	
	// [start] specific function conversion //
	
	/**
	 * This method fills the rule map with the rules.
	 * For each rule a conversion object is added to a hash map, which handles
	 * the conversion individually.
	 * 
	 * Here the rules could be changed or new ones added if necessary.
	 */
	private void fillMap() {
		// Boolean constants
		m_funTrans.put("true", new ConstantFunction("True"));
		m_funTrans.put("false", new ConstantFunction("False"));
		
		// Boolean functions
		m_funTrans.put("and", new AssociativeFunction(
				m_prettyOutput ? " \\<and> " : " & "));
		m_funTrans.put("or", new AssociativeFunction(
				m_prettyOutput ? " \\<or> " : " | "));
		/*
		 * NOTE: implication is right-associative for both
		 *       SMT-LIB and Isabelle, so no change here
		 */
		m_funTrans.put("=>", new AssociativeFunction(
				m_prettyOutput ? " \\<longrightarrow> " : " --> "));
		m_funTrans.put("not", new UnaryFunction(
				m_prettyOutput ? "\\<not>" : "~"));
		/*
		 * NOTE: xor is not a native function in Isabelle,
		 *       but the additional theory defines it
		 */
		m_funTrans.put("xor", new AssociativeFunction(
				m_prettyOutput ? " \\<oplus> " : " xor "));
		m_funTrans.put("ite", new IteFunction());
		
		// (in)equality functions
		m_funTrans.put("=", new ChainableFunction(
				" = "));
		m_funTrans.put("distinct", new DistinctFunction(
				m_prettyOutput ? " \\<noteq> " : " ~= "));
		
		// LA specific functions
		m_funTrans.put("<=", new ChainableFunction(
				m_prettyOutput ? " \\<le> " : " <= "));
		m_funTrans.put("<", new ChainableFunction(" < "));
		m_funTrans.put(">=", new ChainableFunction(
				m_prettyOutput ? " \\<ge> " : " >= "));
		m_funTrans.put(">", new ChainableFunction(" > "));
		m_funTrans.put("+", new AssociativeFunction(" + "));
		// NOTE: '-' can have two meanings, depending on the parameters
		m_funTrans.put("-", new MinusFunction());
		m_funTrans.put("*", new AssociativeFunction(" * "));
		// NOTE: Isabelle automatically converts the type from 'int' to 'real'
		m_funTrans.put("/", new AssociativeFunction(" / "));
		// NOTE: Isabelle and SMT-LIB have different semantics for mod.
		m_funTrans.put("mod", new ModFunction());
		// NOTE: Isabelle and SMT-LIB have different semantics for div.
		m_funTrans.put("div", new AssociativeFunction(" SMTdiv "));
		m_funTrans.put("abs",
				m_prettyOutput ? new AbsFunction() : new UnaryFunction("abs"));
		m_funTrans.put("divisible", new DivisibleFunction());
		m_funTrans.put("to_int", new UnaryFunction("to_int "));
		// NOTE: 'to_real' also exists as shorthand 'real'
		m_funTrans.put("to_real", new UnaryFunction("to_real "));
		m_funTrans.put("is_int", new UnaryFunction("is_int "));
	}
	
	/**
	 * This interface is used for the translation of interpreted functions.
	 */
	private interface IFunction {
		/**
		 * @param function the function
		 */
		public abstract void convert(final ApplicationTerm function);
	}
	
	/**
	 * This abstract class is used for the translation with several function
	 * names.
	 */
	private abstract class AFunction implements IFunction {
		// function name
		protected final String m_name;
		
		/**
		 * @param name the function name
		 */
		public AFunction(final String name) {
			m_name = name;
		}
		
		/**
		 * @param function the function
		 */
		@Override
		public abstract void convert(final ApplicationTerm function);
	}
	
	/**
	 * This class translates the Boolean constants.
	 */
	private class ConstantFunction extends AFunction {
		/**
		 * @param name the function name
		 */
		public ConstantFunction(final String name) {
			super(name);
		}
		
		/**
		 * This method converts a Boolean constant ('true' and 'false').
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			writeString(m_name);
		}
	}
	
	/**
	 * This class translates an associative function.
	 */
	private class AssociativeFunction extends AFunction {
		/**
		 * @param name the function name
		 */
		public AssociativeFunction(final String name) {
			super(name);
		}
		
		/**
		 * This method converts an associative function. This means:
		 * The function may have arbitrarily many parameters in Isabelle.
		 * The function must be binary in principle.
		 * Example: '+'
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length > 1);
			
			writeString("(");
			
			enqueueWalker(new StringWalker(")"));
			for (int i = parameters.length - 1; i > 0; --i) {
				enqueueWalker(new TermConverterWalker(parameters[i]));
				enqueueWalker(new StringWalker(m_name));
			}
			enqueueWalker(new TermConverterWalker(parameters[0]));
		}
	}
	
	/**
	 * This class translates an chainable function.
	 */
	private class ChainableFunction extends AFunction {
		/**
		 * @param name the function name
		 */
		public ChainableFunction(final String name) {
			super(name);
		}
		
		/**
		 * This method converts a chainable function. This means:
		 * The function may only have a constant number of parameters in
		 * Isabelle.
		 * The function must be binary in principle.
		 * Example: '='
		 * 
		 * The translation uses lambda abstraction to not write complicated
		 * terms several times (this is even necessary to avoid duplicate
		 * :named annotations).
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length > 1);
			
			if ( parameters.length == 2) {
				writeString("(");
				
				enqueueWalker(new StringWalker(")"));
				enqueueWalker(new TermConverterWalker(parameters[1]));
				enqueueWalker(new StringWalker(m_name));
				enqueueWalker(new TermConverterWalker(parameters[0]));
			}
			else {
				writeString(m_lambda);
				for (int i = 1; i <= parameters.length; ++i) {
					writeString(" ");
					writeString(LAMBDA_VAR_PREFIX);
					writeString(Integer.toString(i));
				}
				writeString(". (");
				String andInPar = "";
				for (int i = 1; i < parameters.length;) {
					writeString(andInPar);
					andInPar = m_andInPar;
					writeString(LAMBDA_VAR_PREFIX);
					writeString(Integer.toString(i));
					writeString(m_name);
					writeString(LAMBDA_VAR_PREFIX);
					writeString(Integer.toString(++i));
				}
				writeString(")) ");
				
				enqueueWalker(new StringWalker(")"));
				for (int i = parameters.length - 1; i > 0; --i) {
					enqueueWalker(new TermConverterWalker(parameters[i]));
					enqueueWalker(new StringWalker(" "));
				}
				enqueueWalker(new TermConverterWalker(parameters[0]));
			}
		}
	}
	
	/**
	 * This class translates an unary function.
	 */
	private class UnaryFunction extends AFunction {
		/**
		 * @param name the function name
		 */
		public UnaryFunction(final String name) {
			super(name);
		}
		
		/**
		 * This method converts a unary function. This means:
		 * The function has exactly one argument in Isabelle.
		 * Parentheses are added to handle all cases equally.
		 * Examples: 'not, unary -, abs'
		 * 
		 * NOTE: Isabelle interprets '~~p = p' as '~(~(p = p))',
		 *       so parentheses are needed
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length == 1);
			
			writeString("(");
			writeString(m_name);
			
			enqueueWalker(new StringWalker(")"));
			enqueueWalker(new TermConverterWalker(parameters[0]));
		}
	}
	
	/**
	 * This class translates the distinct function.
	 */
	private class DistinctFunction extends AFunction {
		/**
		 * @param name the function name
		 */
		public DistinctFunction(final String name) {
			super(name);
		}
		
		/**
		 * This method converts the distinct function. This means:
		 * The function is not transitive, so every possible combination must
		 * be generated.
		 * Example:
		 * '(distinct (a b c))' means '(a != b) && (a != c) && (b != c)'
		 * 
		 * The translation uses lambda abstraction to not write complicated
		 * terms several times (this is even necessary to avoid duplicate
		 * :named annotations).
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length > 1);
			
			if ( parameters.length == 2) {
				writeString("(");
				
				enqueueWalker(new StringWalker(")"));
				enqueueWalker(new TermConverterWalker(parameters[1]));
				enqueueWalker(new StringWalker(m_name));
				enqueueWalker(new TermConverterWalker(parameters[0]));
			}
			else {
				writeString(m_lambda);
				for (int i = 1; i <= parameters.length; ++i) {
					writeString(" ");
					writeString(LAMBDA_VAR_PREFIX);
					writeString(Integer.toString(i));
				}
				writeString(". (");
				String andInPar = "";
				for (int i = 1; i < parameters.length; ++i) {
					for (int j = i; j < parameters.length;) {
						writeString(andInPar);
						andInPar = m_andInPar;
						writeString(LAMBDA_VAR_PREFIX);
						writeString(Integer.toString(i));
						writeString(m_name);
						writeString(LAMBDA_VAR_PREFIX);
						writeString(Integer.toString(++j));
					}
				}
				writeString(")) ");
				
				enqueueWalker(new StringWalker(")"));
				for (int i = parameters.length - 1; i > 0; --i) {
					enqueueWalker(new TermConverterWalker(parameters[i]));
					enqueueWalker(new StringWalker(" "));
				}
				enqueueWalker(new TermConverterWalker(parameters[0]));
			}
		}
	}
	
	/**
	 * This class translates the minus function.
	 */
	private class MinusFunction implements IFunction {
		// converter for exactly one parameter
		private final UnaryFunction m_unary;
		// converter for more than one parameters
		private final AssociativeFunction m_associative;
		
		/**
		 * constructor
		 */
		public MinusFunction() {
			m_unary = new UnaryFunction("- ");
			m_associative = new AssociativeFunction(" - ");
		}
		
		/**
		 * This method converts the minus ('-') function.
		 * It can be either a sign or an operator, depending on the parameter
		 * count.
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length > 0);
			
			// negative sign
			if (parameters.length == 1) {
				m_unary.convert(function);
			}
			// associative minus operator
			else {
				m_associative.convert(function);
			}
		}
	}
	
	/**
	 * This class translates the ite (if-then-else) function.
	 */
	private class IteFunction implements IFunction {
		/**
		 * This method converts the if-then-else function. This means:
		 * The function has exactly three arguments in Isabelle.
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length == 3);

			writeString("(if ");
			
			enqueueWalker(new StringWalker(")"));
			enqueueWalker(new TermConverterWalker(parameters[2]));
			enqueueWalker(new StringWalker(" else "));
			enqueueWalker(new TermConverterWalker(parameters[1]));
			enqueueWalker(new StringWalker(" then "));
			enqueueWalker(new TermConverterWalker(parameters[0]));
		}
	}
	
	/**
	 * This class translates the modulo function.
	 */
	private class ModFunction implements IFunction {
		/**
		 * This method converts the modulo function. This means:
		 * The function has exactly two arguments in Isabelle.
		 * Example: 'mod'
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length == 2);
			
			writeString("(");
			
			enqueueWalker(new StringWalker(")"));
			enqueueWalker(new TermConverterWalker(parameters[1]));
			enqueueWalker(new StringWalker(" SMTmod "));
			enqueueWalker(new TermConverterWalker(parameters[0]));
		}
	}
	
	/**
	 * This class translates the divisible function.
	 */
	private class DivisibleFunction implements IFunction {
		/**
		 * This method handles the special conversion of the 'divisible'
		 * predicate.
		 * This is necessary due to syntax anomalies in SMT-LIB.
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			final BigInteger[] indices = function.getFunction().getIndices();
			assert ((parameters.length == 1) && (indices.length == 1));
			
			writeString("(");
			writeString(indices[0].toString());
			writeString(" dvd ");
			
			enqueueWalker(new StringWalker(")"));
			enqueueWalker(new TermConverterWalker(parameters[0]));
		}
	}
	
	/**
	 * This class translates the abs (absolute value) function with pretty
	 * printing.
	 */
	private class AbsFunction implements IFunction {
		/**
		 * This method handles the special conversion of the 'abs' function
		 * with pretty printing, which is written '\<bar> expression \<bar>'.
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm function) {
			final Term[] parameters = function.getParameters();
			assert (parameters.length == 1);
			
			writeString(" \\<bar>");
			
			enqueueWalker(new StringWalker("\\<bar> "));
			enqueueWalker(new TermConverterWalker(parameters[0]));
		}
	}
	
	/**
	 * This method converts non-intern functions, i.e., functions not defined
	 * in SMT-LIB.
	 * Prefix notation is used.
	 * 
	 * @param function non-intern function symbol
	 * @param parameters parameters of the function
	 */
	private void toNoninternFunction(final FunctionSymbol function,
			Term[] parameters) {
		if (parameters.length > 0) {
			writeString("(");
			writeSortString(function);
			
			enqueueWalker(new StringWalker(")"));
			for (int i = parameters.length - 1; i >= 0; --i) {
				enqueueWalker(new TermConverterWalker(parameters[i]));
				enqueueWalker(new StringWalker(" "));
			}
		}
		else {
			writeSortString(function);
		}
	}
	
	/**
	 * This method writes a function string.
	 * The parameter and return sorts are also written if globally enabled.
	 * 
	 * @param functionSymbol the function symbol
	 */
	private void writeSortString(final FunctionSymbol functionSymbol) {
		// non-theory Isabelle-interpreted functions
		String functionName = m_function2compFunction.get(functionSymbol);
		
		// only print types the first time and also store compatible names
		if (functionName != null) {
			writeString(functionName);
			return;
		}
		
		functionName = toCompatibleString(functionSymbol.getName());
		
		if (m_printTypes) {
			final String arrow = m_prettyOutput ? "\\<Rightarrow>" : "=>";
			final StringBuilder builder = new StringBuilder();
			
			builder.append("(");
			builder.append(functionName);
			builder.append("::");
			for (Sort paramSort : functionSymbol.getParameterSorts()) {
				builder.append(getSingleSortString(paramSort));
				builder.append(arrow);
			}
			builder.append(
					getSingleSortString(functionSymbol.getReturnSort()));
			builder.append(")");
			
			functionName = builder.toString();
		}
		
		writeString(functionName);
		m_function2compFunction.put(functionSymbol, functionName);
	}
	
	/**
	 * This method returns the Isabelle name for a given sort.
	 * 
	 * @param sort the sort
	 * @return the Isabelle name of the sort
	 */
	public String getSingleSortString(final Sort sort) {
		final String sortString = sort.getName();
		if (sortString == "Int") {
			return "int";
		}
		else if (sortString == "Real") {
			return "real";
		}
		else if (sortString == "Bool") {
			return "bool";
		}
		else {
			assert (! sort.isInternal());
			return "'a";
		}
	}
	
	/**
	 * This method converts user-defined strings to Isabelle compatible
	 * strings.
	 * 
	 * @param functionSymbol the function symbol
	 * @return the modified function symbol
	 */
	String toCompatibleString(final String functionSymbol) {
		final char[] origin = functionSymbol.toCharArray();
		final StringBuilder builder = new StringBuilder();
		builder.append("smt_");
		
		final Pattern valid = Pattern.compile("[a-zA-Z0-9]");
		
		for (int i = 0; i < origin.length; ++i) {
			final String next = Character.toString(origin[i]);
			if (valid.matcher(next).matches()) {
				builder.append(next);
			}
			else {
				builder.append("_");
				builder.append(next.codePointAt(0));
			}
		}
		
		return builder.toString();
	}
	
	// [end] specific function conversion //
	
	// [start] additional functionalities //
	
	/**
	 * This method is called to indicate the start or end of the proof mode.
	 */
	public void switchProofMode() {
		m_namedList = null;
		m_namedStack = null;
		m_function2compFunction.clear();
	}
	
	/**
	 * This method converts an assertion and returns the :named definitions.
	 * 
	 * @param assertion the assertion
	 * @return a list with the :named definitions
	 */
	public LinkedList<NamedWrapper> convertAssertion(final Term assertion) {
		m_namedList = new LinkedList<NamedWrapper>();
		m_namedStack = new ArrayDeque<NamedWrapper>();
		m_printTypes = true;
		
		convert(assertion);
		
		m_printTypes = false;
		return m_namedList;
	}
	
	/**
	 * This method supports temporarily writing to a different output
	 * appendable. Afterwards the old appendable is used again.
	 * 
	 * @param term the SMT-LIB term
	 * @param appendable the temporary appendable
	 */
	public void convertToAppendable(final Term term,
			final Appendable appendable) {
		Appendable tmp = m_appendable;
		m_appendable = appendable;
		convert(term);
		m_appendable = tmp;
	}
	
	/**
	 * This method writes to another appendable and prints (numeric) types.
	 * It is used by the LA lemma.
	 * 
	 * @param term the SMT-LIB term
	 * @param appendable the lemma appendable
	 */
	public void convertWithTypes(final Term term,
			final Appendable appendable) {
		m_printTypes = true;
		m_namedStack = null;
		convertToAppendable(term, appendable);
		m_printTypes = false;
	}
	
	/**
	 * This method provides writing rational numbers without converting them to
	 * decimal numbers (which could be non-terminating).
	 * 
	 * This is only needed in the conversion of real arithmetic lemma, so it
	 * directly converts the data structure used there. The result is written
	 * to the appendable and looks like:
	 * 'f1 * x1 + ... + fn * xn + c', where the fi are factors, the xi are
	 * arbitrary terms seen as variables, and c is a constant. If an fi is 1 or
	 * the c is 0, it is ignored.
	 * 
	 * @param constant the constant
	 * @param collection data structure of LA lemma
	 * @param appendable lemma appendable
	 */
	public void convertFactorMap(Rational constant,
			final Collection<Map.Entry<Term, FactorWrapper>> collection,
			final Appendable appendable) {
		assert (collection.size() > 0);
		
		final Appendable tmp = m_appendable;
		m_appendable = appendable;
		
		writeString("(");
		
		// variables
		String plus = "";
		for (Map.Entry<Term, FactorWrapper> tuple : collection) {
			writeString(plus);
			plus = " + ";
			
			Rational rational = tuple.getValue().m_factor;
			boolean isNegative = rational.isNegative();
			if (isNegative) {
				rational = rational.negate();
			}
			
			if (rational.isIntegral()) {
				if (isNegative) {
					writeString("- ");
				}
				writeString(rational.numerator().toString());
				writeString(" * ");
				convert(tuple.getKey());
			}
			else {
				if (isNegative) {
					writeString("- ");
				}
				writeString("(");
				writeString(rational.numerator().toString());
				writeString(" / ");
				writeString(rational.denominator().toString());
				writeString(") * ");
				convert(tuple.getKey());
			}
		}
		
		// constant
		if (! constant.equals(Rational.ZERO)) {
			boolean isNegative = constant.isNegative();
			if (isNegative) {
				constant = constant.negate();
			}

			writeString(" + ");
			
			if (constant.isIntegral()) {
				if (isNegative) {
					writeString("- ");
				}
				writeString(constant.numerator().toString());
			}
			else {
				if (isNegative) {
					writeString("- ");
				}
				writeString("(");
				writeString(constant.numerator().toString());
				writeString(" / ");
				writeString(constant.denominator().toString());
				writeString(")");
			}
		}
		
		writeString(")");
		
		m_appendable = tmp;
	}
	
	public String getFunctionName(final FunctionSymbol functionSymbol) {
		String name = m_function2compFunction.get(functionSymbol);
		if (name == null) {
			name = toCompatibleString(functionSymbol.getName());
		}
		assert (name != null);
		return name;
	}
	
	// [end] additional functionalities //
	
	// [start] stack related //
	
	/**
	 * This method writes a string to the appendable.
	 * 
	 * @param string string that needs not use the stack
	 * @throws RuntimeException thrown if an IOException is caught
	 */
	private void writeString(final String string) {
		try {
			m_appendable.append(string);
        } catch (IOException e) {
            throw new RuntimeException("Appender throws IOException", e);
        }
	}
	
	// [end] stack related //
}