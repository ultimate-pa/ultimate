package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeSizeCalculator;

/** Given a formula in NNF only consisting of "and" and "or", as well as "not" at innermost positions,
 * transforms it into CNF / DNF applying distribution. The structure will be flat, meaning that
 * for example "and"s within "and"s are not allowed. */
public class NNFtoCDNFTransformer extends TermTransformer {
	/** The name of the function symbol expected to be at root level. */
	private String outer;
	/** The name of the function symbol expected to be one level deeper from root level. */
	private String inner;
	private int currentTermSizeIncrease;
	private int maximumTermSizeIncrease;
	private HashMap<Term, Integer> convertedCache;
	
	/** @param maximumTermSizeIncrease Give maximumTermSizeIncrease a negative value if you don't want to check if it is exceeded
	 * during transformation. */
	public NNFtoCDNFTransformer(TargetNF targetNormalForm, HashMap<Term, Integer> convertedCache, int maximumTermSizeIncrease) {
		this.currentTermSizeIncrease = 0;
		this.maximumTermSizeIncrease = maximumTermSizeIncrease;
		this.convertedCache = convertedCache;
		if (targetNormalForm == TargetNF.CNF) {
			outer = "and";
			inner = "or";
		} else if (targetNormalForm == TargetNF.DNF) {
			outer = "or";
			inner = "and";
		}
	}
	
	public enum TargetNF {CNF, DNF}
	
	/** @throws ExceedsMaxTreeSizeException Will throw this if you set a non-negative maximumTermSizeIncrease in 
	 * the constructor of this NNFtoCDNFTransformer if it is exceeded during conversion. */
	@Override
	protected void convert(Term term) {
		//TreeIC3.logger().debug("convert "+term.toStringDirect());
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol function = appTerm.getFunction();
			String functionName = function.getName();
			Term[] params = appTerm.getParameters();
			Theory theory = appTerm.getTheory();
			
			if (functionName.equals(outer)) {
				Term flattened = flatten(theory, outer, params); 
				if (flattened != null) {
					pushTerm(flattened);
					return;
				}
				// Check if there is any param that can be further transformed
				// If yes, push our term and try again
				// If no, set result
				boolean worked = false;
				for (int i = 0; i < params.length; i++) {
					Term param = params[i];
					if (param instanceof ApplicationTerm) {
						ApplicationTerm contentAppTerm = (ApplicationTerm) param; 
						String contentFunctionName = contentAppTerm.getFunction().getName();
						if (contentFunctionName.equals(inner)) {
							Term transformedParam = tryInnerConversion(contentAppTerm);
							if (transformedParam != null) {
								params[i] = transformedParam;
								worked = true;
							}
						}
					}
				}
				if (worked) {
					Term transformedTerm = theory.term(outer, params);
					pushTerm(transformedTerm);
				} else {
					setResult(term);
					//TreeIC3.logger().debug("setResult "+term);
				}
			} else if (functionName.equals(inner)) {
				Term transformedTerm = tryInnerConversion(appTerm);
				if (transformedTerm != null) {
					pushTerm(transformedTerm);
				} else {
					setResult(term);
					//TreeIC3.logger().debug("setResult "+term);
				}
			} else {
				setResult(term);
				//TreeIC3.logger().debug("setResult "+term);
			}
		} else {
			setResult(term);
			//TreeIC3.logger().debug("setResult "+term);
		}
	}
	
	
	private Term tryInnerConversion(ApplicationTerm appTerm) {
		FunctionSymbol function = appTerm.getFunction();
		String functionName = function.getName();
		Term[] params = appTerm.getParameters();
		Theory theory = appTerm.getTheory();

		assert(functionName.equals(inner));
		Term flattened = flatten(theory, inner, params);
		if (flattened != null) {
			return flattened;
		}
		// we have to look if there exists an outer function symbol inside an element,
		// then we could apply distribution
		for (int i = 0; i < params.length; i++) {
			if (params[i] instanceof ApplicationTerm) {
				ApplicationTerm contentAppTerm = (ApplicationTerm) params[i];
				FunctionSymbol contentFunction = contentAppTerm.getFunction();
				String contentFunctionName = contentFunction.getName();
				Term[] contentParams = contentAppTerm.getParameters();
				if (contentFunctionName.equals(outer)) {
					//TreeIC3.logger().debug("Distribution rule");
					// distribute all other params over params[i], meaning over its contentParams
					// determine the other params to distribute:
					ArrayList<Term> otherTerms = new ArrayList<Term>();
					for (int j = 0; j < i; j++) {
						otherTerms.add(params[j]);
					}
					for (int j = i+1; j < params.length; j++) {
						otherTerms.add(params[j]);
					}
					
					// NOTE that distribution is the only operation of this transformer which
					// increases the tree size.
					// calculate the tree size increase:
					int otherTermsSize = 0;
					for (Term otherTerm : otherTerms) {
						Integer termSize = TreeSizeCalculator.calcTreeSize(otherTerm, convertedCache);
						assert(termSize != null);
						otherTermsSize += termSize;
					}
					addCurrentTermSizeIncrease((contentParams.length - 1) * (params.length - 1 + otherTermsSize));

					// form the distributions:
					ArrayList<Term> distributions = new ArrayList<Term>();
					for (Term contentParam : contentParams) {
						ArrayList<Term> distribution = new ArrayList<Term>(otherTerms);
						distribution.add(contentParam);
						Term distributed = theory.term(inner, distribution.toArray(new Term[distribution.size()]));
						distributions.add(distributed);
					}
					Term distributedTerm = theory.term(outer, distributions.toArray(new Term[distributions.size()]));
					return distributedTerm;
				}
			}
		}
		// if we ran through the for-loop without applying distribution,
		// we can return null:
		return null;
	}
	
	/** Will flatten the given term (functionName, params) for one depth. For example, if we have a
	 * conjunction, will insert all sub-conjunctions for one depth. Will return
	 * the new term if successful. Will return null if unsuccessful. */
	private static Term flatten(Theory theory, String functionName, Term[] params) {
		boolean worked = false;
		ArrayList<Term> newParams = new ArrayList<Term>();
		for (Term contentTerm : params) {
			if (contentTerm instanceof ApplicationTerm) {
				ApplicationTerm contentAppTerm = (ApplicationTerm) contentTerm;
				FunctionSymbol contentFunction = contentAppTerm.getFunction();
				String contentFunctionName = contentFunction.getName();
				Term[] contentParams = contentAppTerm.getParameters();
				if (contentFunctionName.equals(functionName)) {
					for (Term contentContentTerm : contentParams) {
						newParams.add(contentContentTerm);
						worked = true;
					}
				} else {
					newParams.add(contentTerm);
				}
			} else {
				newParams.add(contentTerm);
			}
		}
		if (worked) {
			//TreeIC3.logger().debug("Structure flattened.");
			ApplicationTerm flattened = theory.term(functionName,
					newParams.toArray(new Term[newParams.size()]));
			return flattened;
		} else {
			return null;
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
