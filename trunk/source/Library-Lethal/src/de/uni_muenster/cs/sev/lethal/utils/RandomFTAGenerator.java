/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.utils;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import de.uni_muenster.cs.sev.lethal.languages.RegularTreeLanguage;
import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;

/**
 * Class to generate random finite tree automata.
 * 
 * @author Peter Lammich
 */
public class RandomFTAGenerator {

	private int numStates;
	private int numSymbols;
	private int maxArity;
	private int numRules;
	private int numFinal;

	boolean langGen=false;
	private int [] arities; 
	private State [] states;
	private RankedSymbol [] symbols;
	private Random rg = null;

	/**
	 * Default seed for the random number generator underlying the random FTA generation.
	 */
	public static final long DFLT_SEED = 0x678253781254378L;


	/**
	 * Initializes the generator to default values.
	 */
	public RandomFTAGenerator(){
		this(50,50,2,1500,1);
	}


	/**
	 * Initializes the generator with the specified values.
	 * 
	 * @param numStates Number of states of the generated automata. 
	 * @param numSymbols Number of symbols. Must be greater than 0.
	 * @param maxArity Maximum arity. The generated function symbols' arities will be spread equally between [0..maxArity]. However, 
	 * 	  there will be at least one symbol with arity 0. 
	 * @param numRules Number of rules.
	 * @param numFinal Number of final states.
	 * @param seed Seed for the random number generator
	 */
	public RandomFTAGenerator(int numStates,int numSymbols,int maxArity,int numRules,int numFinal, long seed) {
		if (!(numSymbols > 0)) throw new IllegalArgumentException("numSymbols must be >0");
		this.numStates = numStates;
		this.states = new State [numStates];
		this.numSymbols = numSymbols;
		this.symbols = new RankedSymbol [numSymbols];
		arities = new int [numSymbols];
		this.maxArity = maxArity;
		this.numRules = numRules;
		this.numFinal = numFinal;
		rg = new Random(seed);		
	}
	
	/**
	 * Initializes the generator with the specified values.
	 * 
	 * @param numStates Number of states of the generated automata. 
	 * @param numSymbols Number of symbols. Must be greater than 0.
	 * @param maxArity Maximum arity. The generated function symbols' arities will be spread equally between [0..maxArity]. However, 
	 * 	  there will be at least one symbol with arity 0. 
	 * @param numRules Number of rules.
	 * @param numFinal Number of final states.
	 */
	public RandomFTAGenerator(int numStates,int numSymbols,int maxArity,int numRules,int numFinal){
		this(numStates, numSymbols, maxArity, numRules, numFinal, DFLT_SEED);
	}

	/**
	 * Get the random number generator.
	 * @return Random number generator
	 */
	public Random getRg() {
		return rg;
	}

	/**
	 * Set the random number generator. Subsequent operations will be based on the new random number generator.
	 * 
	 * Note that setting the random number generator immediately after constructing this class is sufficient to have all
	 * randomness based on the new generator, as the default generator will not be used before the first call to a <code>generateXXX</code>-method.
	 * @param rg New Random number generator. Must not be null.
	 */
	public void setRg(Random rg) {
		assert rg!=null;
		this.rg = rg;
	}

	
	
	/**
	 * Returns all generated symbols.
	 * 
	 * @return all generated Symbols
	 */
	public RankedSymbol[] getSymbols() {
		if (!langGen)
			generateAlphabet();
		return symbols;
	}


	/**
	 * (Re)Generates the current alphabet.
	 * This method generates an alphabet by choosing the arities of the function symbols.
	 * The generated alphabet will be used for all subsequently generated automata. 
	 */
	public void generateAlphabet() {
		// Fill arities
		boolean haveZero;
		do {
			haveZero = false;
			for (int i=0;i<numSymbols;++i) {
				arities[i]=rg.nextInt(maxArity+1);
				if (arities[i]==0) haveZero=true;
			}
		} while (!haveZero);

		// Symbols
		for (int i=0;i<numSymbols;++i) {
			symbols[i] = new StdNamedRankedSymbol<Integer>(i,arities[i]);
		}

		langGen=true;
	}

	/**
	 * Generates an automaton. The automaton will contain randomly generated rules that match the current alphabet.
	 * If no alphabet was generated yet, a call to {@link #generateAlphabet()} will be issued.
	 * @return Random automaton
	 */
	public EasyFTA generateRaw() {

		if (!langGen) generateAlphabet();

		EasyFTA res = new EasyFTA();
		// States
		for (int i=0;i<numStates;++i) {
			states[i] = new NamedState<Integer>(i);
		}

		// Final states
		for (int i=0;i<numFinal;++i) res.addToFinals(states[i]);

		// Rules
		for (int i=0;i<numRules;++i) {
			// Create rule 
			RankedSymbol f = symbols[rg.nextInt(numSymbols)];
			State dest = states[rg.nextInt(numStates)];
			List<State> source = new ArrayList<State>(f.getArity());
			for (int j=0;j<f.getArity();++j)
				source.add(states[rg.nextInt(numStates)]);

			res.addRule(f,source,dest);
			//res.createRule(f,source,dest);
		}

		return res;
	}


	/**
	 * Generates a random, reduced automaton.
	 * The result is obtained by generating a random automaton and then reducing it.
	 * Note that the result is <em>not</em> equally distributed over the space of <em>reduced</em> automata. 
	 * @return Reduced, random automaton
	 */
	public EasyFTA generateReduced() {
		return EasyFTAOps.reduceFull(generateRaw());
	}

	/**
	 * Generates an automaton that accepts no trees with a depth smaller than or equal to minDepth.
	 * Note that this function may need exponential space and time in minDepth. 
	 * @param minDepth Only trees with a higher depth will be accepted
	 * @return Random automaton.
	 */
	@SuppressWarnings("unchecked")
	public EasyFTA generateStripped(int minDepth) {
		EasyFTA f1 = generateReduced();
		if (minDepth>0) {
			RegularTreeLanguage<RankedSymbol> rtl = new RegularTreeLanguage<RankedSymbol>(f1);
			System.out.println("restrict");
			GenFTA<RankedSymbol, State> fs = (GenFTA<RankedSymbol, State>)rtl.restrictToMaxHeight(minDepth).getFTA();
			System.out.println("diff");

			EasyFTA f3 = EasyFTAOps.difference(f1, fs);
			System.out.println("done");
			return f3;
		} else return f1;
	}




}
