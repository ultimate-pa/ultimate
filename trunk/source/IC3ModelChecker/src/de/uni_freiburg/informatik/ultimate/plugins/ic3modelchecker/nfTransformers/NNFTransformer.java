package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers;

import java.util.Arrays;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeIC3;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeSizeCalculator;

/** Converts a formula into NNF such that it only consists of "and", "or", "not", and atomic formulas. 
 * The negation symbols are standing at the innermost positions in front of the atomic formulas. */
public class NNFTransformer extends TermTransformer {
	private int currentTermSizeIncrease;
	private int maximumTermSizeIncrease;
	private HashMap<Term, Integer> convertedCache;
	
	/** @param maximumTermSizeIncrease Give maximumTermSizeIncrease a negative value if you don't want to check if it is exceeded
	 * during transformation. */
	public NNFTransformer(HashMap<Term, Integer> convertedCache, int maximumTermSizeIncrease) {
		this.currentTermSizeIncrease = 0;
		this.maximumTermSizeIncrease = maximumTermSizeIncrease;
		this.convertedCache = convertedCache;
	}

	/** @throws ExceedsMaxTreeSizeException Will throw this if you set a non-negative maximumTermSizeIncrease in 
	 * the constructor of this NNFTransformer if it is exceeded during conversion. */
	@Override
	protected void convert(Term term) {
		TreeIC3.logger().debug("convert "+term.toStringDirect());
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol function = appTerm.getFunction();
			String functionName = function.getName();
			Term[] params = appTerm.getParameters();
			Theory theory = term.getTheory();
			
			if (functionName.equals("not")) {
				Term content = params[0];
				if (content instanceof ApplicationTerm) {
					ApplicationTerm contentAppTerm = (ApplicationTerm) content;
					FunctionSymbol contentFunction = contentAppTerm.getFunction();
					String contentFunctionName = contentFunction.getName();
					Term[] contentParams = contentAppTerm.getParameters();
					
					if (contentFunctionName.equals("not")) {
						// double negation
						TreeIC3.logger().debug("pushTerm "+contentParams[0].toStringDirect());
						pushTerm(contentParams[0]);
					} else if (contentFunctionName.equals("or")) {
						assert(contentParams.length > 1);
						// move negation inward via DeMorgan
						BuildApplicationTerm andBuilder = new BuildApplicationTerm(
								theory.term("and", contentParams));
						enqueueWalker(andBuilder);
						for (int i = contentParams.length-1; i >= 0; i--) {
							Term toPush = theory.term("not",contentParams[i]);
							TreeIC3.logger().debug("pushTerm "+toPush.toStringDirect());
							pushTerm(toPush);
						}
					} else if (contentFunctionName.equals("xor")) {
						Term replacement = theory.term("distinct", contentParams[0], contentParams[1]);
						for (int i = 2; i < contentParams.length; i++) {
							replacement = theory.term("distinct", replacement, contentParams[i]);
						}
						pushTerm(theory.term("not", replacement));
					} else if (contentFunctionName.equals("and")) {
						// move negation inward via DeMorgan
						BuildApplicationTerm orBuilder = new BuildApplicationTerm(
								theory.term("or", contentParams));
						enqueueWalker(orBuilder);
						for (int i = contentParams.length-1; i >= 0; i--) {
							Term toPush = theory.term("not",contentParams[i]);
							TreeIC3.logger().debug("pushTerm "+toPush.toStringDirect());
							pushTerm(toPush);
						}
					} else if (contentFunctionName.equals("=>")) {
						BuildApplicationTerm andBuilder = new BuildApplicationTerm(
								theory.term("and", contentParams));
						enqueueWalker(andBuilder);
						Term toPush = theory.term("not", contentParams[contentParams.length-1]);
						TreeIC3.logger().debug("pushTerm "+toPush.toStringDirect());
						pushTerm(toPush);
						for (int i = contentParams.length-2; i >= 0; i--) {
							TreeIC3.logger().debug("pushTerm "+contentParams[i]);
							pushTerm(contentParams[i]);
						}
					} else if (contentFunctionName.equals("ite") && contentFunction.getReturnSort() == theory.getBooleanSort()) {
						Term condTerm = contentParams[0];
						Term thenTerm = contentParams[1];
						Term elseTerm = contentParams[2];
						BuildApplicationTerm andBuilder = new BuildApplicationTerm(
								theory.term("and", theory.TRUE, theory.TRUE));
						enqueueWalker(andBuilder);
						TreeIC3.logger().debug("pushTerms for ite");
						pushTerm(theory.term("or", condTerm, theory.term("not",elseTerm)));
						pushTerm(theory.term("or", theory.term("not", condTerm),
													theory.term("not", thenTerm)));
						Integer condTermSize = TreeSizeCalculator.calcTreeSize(condTerm, convertedCache);
						assert(condTermSize != null);
						addCurrentTermSizeIncrease(2 + condTermSize);
					} else if (contentFunctionName.equals("=")) {
						// Right now only deals with formulas (as "iff")
						if (contentParams.length > 2) {
							Term[] placeholder = new Term[contentParams.length-1];
							Arrays.fill(placeholder, theory.TRUE);
							BuildApplicationTerm orBuilder = new BuildApplicationTerm(
									theory.term("or", placeholder));
							enqueueWalker(orBuilder);
							for (int i = contentParams.length-2; i >= 0; i--) {
								Term toPush = theory.term("not", theory.term("=", contentParams[i+1], contentParams[i])); 
								pushTerm(toPush);
							}
							for (int i = contentParams.length-2; i >= 1; i--) {
								Integer contentParamSize = TreeSizeCalculator.calcTreeSize(contentParams[i], convertedCache);
								assert(contentParamSize != null);
								addCurrentTermSizeIncrease(1 + contentParamSize);
							}
						} else if (contentFunction.getParameterSort(0) == theory.getBooleanSort()) {
							BuildApplicationTerm andBuilder = new BuildApplicationTerm(
									theory.term("and", theory.TRUE, theory.TRUE));
							enqueueWalker(andBuilder);
							Term first = contentParams[0];
							Term second = contentParams[1];
							pushTerm(theory.term("or", theory.term("not", first), theory.term("not", second)));
							pushTerm(theory.term("or", first, second));
							Integer firstSize = TreeSizeCalculator.calcTreeSize(first, convertedCache);
							assert(firstSize != null);
							Integer secondSize = TreeSizeCalculator.calcTreeSize(second, convertedCache);
							assert(secondSize != null);
							addCurrentTermSizeIncrease(2 + firstSize + secondSize);
						} else {
							TreeIC3.logger().debug("setResult "+term.toStringDirect());
							setResult(term);
						}
					} else if (contentFunctionName.equals("distinct")) {
						// Reduce to "="
						int numberOfComparisons = contentParams.length * (contentParams.length-1) / 2;
						if (numberOfComparisons > 1) {
							Term[] placeholder = new Term[numberOfComparisons];
							Arrays.fill(placeholder, theory.TRUE);
							BuildApplicationTerm orBuilder = new BuildApplicationTerm(
									theory.term("or", placeholder));
							enqueueWalker(orBuilder);
							addCurrentTermSizeIncrease(2*numberOfComparisons-contentParams.length);
							for (Term contentParam : contentParams) {
								Integer contentParamSize = TreeSizeCalculator.calcTreeSize(contentParam, convertedCache);
								assert(contentParamSize != null);
								addCurrentTermSizeIncrease((contentParams.length-2) * contentParamSize);
							}
						}
						for (int first = contentParams.length-2; first >= 0; first--) {
							for (int second = contentParams.length-1; second >= first+1; second--) {
								Term toPush = theory.term("=", contentParams[first], contentParams[second]);
								pushTerm(toPush);
							}
						}
					} else {
						TreeIC3.logger().debug("setResult "+term.toStringDirect());
						setResult(term);
					}
				} else if (content instanceof LetTerm) {
					throw new RuntimeException("NNFTransformer: Cannot handle LetTerm!");
				} else {
					TreeIC3.logger().debug("setResult "+term.toStringDirect());
					setResult(term);
				}
			} else if (functionName.equals("or")) {
				BuildApplicationTerm orBuilder = new BuildApplicationTerm(
						theory.term("or", params));
				enqueueWalker(orBuilder);
				for (int i = params.length-1; i >= 0; i--) {
					TreeIC3.logger().debug("pushTerm "+params[i].toStringDirect());
					pushTerm(params[i]);
				}
			} else if (functionName.equals("xor")) {
				Term replacement = theory.term("distinct", params[0], params[1]);
				for (int i = 2; i < params.length; i++) {
					replacement = theory.term("distinct", replacement, params[i]);
				}
				pushTerm(replacement);
			} else if (functionName.equals("and")) {
				BuildApplicationTerm andBuilder = new BuildApplicationTerm(
						theory.term("and", params));
				enqueueWalker(andBuilder);
				for (int i = params.length-1; i >= 0; i--) {
					TreeIC3.logger().debug("pushTerm "+params[i].toStringDirect());
					pushTerm(params[i]);
				}
			} else if (functionName.equals("=>")) {
				BuildApplicationTerm orBuilder = new BuildApplicationTerm(
						theory.term("or", params));
				enqueueWalker(orBuilder);
				TreeIC3.logger().debug("pushTerm "+params[params.length-1].toStringDirect());
				pushTerm(params[params.length-1]);
				for (int i = params.length-2; i >= 0; i--) {
					Term toPush = theory.term("not", params[i]);
					TreeIC3.logger().debug("pushTerm "+toPush.toStringDirect());
					pushTerm(toPush);
				}
			} else if (functionName.equals("ite") && function.getReturnSort() == theory.getBooleanSort()) {
				// Right now only deals with formulas
				Term condTerm = params[0];
				Term thenTerm = params[1];
				Term elseTerm = params[2];
				BuildApplicationTerm orBuilder = new BuildApplicationTerm(
						theory.term("or", theory.TRUE, theory.TRUE));
				enqueueWalker(orBuilder);
				TreeIC3.logger().debug("pushTerms for ite");
				pushTerm(theory.term("and", theory.term("not", condTerm), elseTerm));
				pushTerm(theory.term("and", condTerm, thenTerm));
				Integer condTermSize = TreeSizeCalculator.calcTreeSize(condTerm, convertedCache);
				assert(condTermSize != null);
				addCurrentTermSizeIncrease(2 + condTermSize);
			} else if (functionName.equals("=")) {
				if (params.length > 2) {
					Term[] placeholder = new Term[params.length-1];
					Arrays.fill(placeholder, theory.TRUE);
					BuildApplicationTerm andBuilder = new BuildApplicationTerm(
							theory.term("and", placeholder));
					enqueueWalker(andBuilder);
					for (int i = params.length-2; i >= 0; i--) {
						Term toPush = theory.term("=", params[i+1], params[i]); 
						pushTerm(toPush);
					}
					for (int i = params.length-2; i >= 1; i--) {
						Integer paramSize = TreeSizeCalculator.calcTreeSize(params[i], convertedCache);
						assert(paramSize != null);
						addCurrentTermSizeIncrease(1 + paramSize);
					}
				} else if (function.getParameterSort(0) == theory.getBooleanSort()) {
					// Right now only deals with formulas (as "iff")
					BuildApplicationTerm orBuilder = new BuildApplicationTerm(
							theory.term("or", theory.TRUE, theory.TRUE));
					enqueueWalker(orBuilder);
					Term first = params[0];
					Term second = params[1];
					pushTerm(theory.term("and", theory.term("not", first), theory.term("not", second)));
					pushTerm(theory.term("and", first, second));
					Integer firstSize = TreeSizeCalculator.calcTreeSize(first, convertedCache);
					assert(firstSize != null);
					Integer secondSize = TreeSizeCalculator.calcTreeSize(second, convertedCache);
					assert(secondSize != null);
					addCurrentTermSizeIncrease(2 + firstSize + secondSize);
				} else {
					TreeIC3.logger().debug("setResult "+term.toStringDirect());
					setResult(term);
				}
			} else if (functionName.equals("distinct")) {
				// Reduce to "="
				int numberOfComparisons = params.length * (params.length-1) / 2;
				if (numberOfComparisons > 1) {
					Term[] placeholder = new Term[numberOfComparisons];
					Arrays.fill(placeholder, theory.TRUE);
					BuildApplicationTerm andBuilder = new BuildApplicationTerm(
							theory.term("and", placeholder));
					enqueueWalker(andBuilder);
					addCurrentTermSizeIncrease(2*numberOfComparisons-params.length);
					for (Term param : params) {
						Integer paramSize = TreeSizeCalculator.calcTreeSize(param, convertedCache);
						assert(paramSize != null);
						addCurrentTermSizeIncrease((params.length-2) * paramSize);
					}
				}
				for (int first = params.length-2; first >= 0; first--) {
					for (int second = params.length-1; second >= first+1; second--) {
						Term toPush = theory.term("not", theory.term("=", params[first], params[second]));
						pushTerm(toPush);
					}
				}
			} else {
				TreeIC3.logger().debug("setResult "+term.toStringDirect());
				setResult(term);
			}
		} else if (term instanceof LetTerm) {
			throw new RuntimeException("NNFTransformer: Cannot handle LetTerm!");
		} else {
			TreeIC3.logger().debug("setResult "+term.toStringDirect());
			setResult(term);
		}
	}
	
	public void setCurrentTermSizeIncrease(int currentTermSizeIncrease) {
		this.currentTermSizeIncrease = currentTermSizeIncrease;
	}
	public int getCurrentTermSizeIncrease() {
		return currentTermSizeIncrease;
	}
	public void setMaximumTermSizeIncrease(int maximumTermSizeIncrease) {
		this.maximumTermSizeIncrease = maximumTermSizeIncrease;
	}
	public int getMaximumTermSizeIncrease() {
		return maximumTermSizeIncrease;
	}
	
	private void addCurrentTermSizeIncrease(int toAdd) throws ExceedsMaxTreeSizeException {
		assert(toAdd >= 0);
		currentTermSizeIncrease += toAdd;
		if (maximumTermSizeIncrease >= 0 && currentTermSizeIncrease > maximumTermSizeIncrease)
			throw new ExceedsMaxTreeSizeException();
	}
}


