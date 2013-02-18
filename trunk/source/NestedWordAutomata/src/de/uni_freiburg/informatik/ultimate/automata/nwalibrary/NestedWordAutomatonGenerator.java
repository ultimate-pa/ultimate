package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * Class that provides the method {@code generateAutomaton()} for randomly
 * generating connected NFAs. Here connected means that every state is reachable
 * from the (unique) initial state.
 * 
 * @author Fabian Reiter
 */
public class NestedWordAutomatonGenerator {
	
	private Random m_Random;
	
	public NestedWordAutomatonGenerator() {
		m_Random = new Random();
	}
	
	/**
	 * @param seed
	 *            initial seed for the internal random number generator
	 */
	public NestedWordAutomatonGenerator(long seed) {
		m_Random = new Random(seed);
	}
	
	/**
	 * @param random
	 *            random number generator to be used by the automaton generator
	 */
	public NestedWordAutomatonGenerator(Random random) {
		m_Random = random;
	}
	
	public void setRandomSeed(long seed) {
		m_Random.setSeed(seed);
	}
	
	/**
	 * @param alphabetSize
	 *            number of letters of the alphabet
	 * @param size
	 *            number of states of the automaton
	 * @param internalTransitionDensity
	 *            fraction of possible transitions that actually exist in the
	 *            automaton (number between 0 and 1)
	 * @param acceptanceDensity
	 *            fraction of states that are accepting (number between 0 and 1)
	 * @return a randomly generated NFA that fulfills the given specification
	 */
	public INestedWordAutomaton<String,String> generateAutomaton(
							int alphabetSize, int size, 
							double internalTransitionDensity,
							double callTransitionProbability,
							double returnTransitionProbability,
							double acceptanceDensity)
				throws IllegalArgumentException {
		
		boolean isFiniteAutomaton = (callTransitionProbability == 0 
										&& returnTransitionProbability == 0);
		// ────────────────────────────────────────────────────────────────────
		// Check user input and compute num. of transitions & accepting states.
		//
		if (size <= 0)
			throw new IllegalArgumentException(
								"Automaton size must be strictly positive.");
		if (alphabetSize <= 0)
			throw new IllegalArgumentException(
								"Alphabet size must be strictly positive.");
		if (internalTransitionDensity < 0 || internalTransitionDensity > 1)
			throw new IllegalArgumentException(
								"Transition density must be between 0 and 1.");
		if (acceptanceDensity < 0 || acceptanceDensity > 1)
			throw new IllegalArgumentException(
								"Acceptance density must be between 0 and 1.");
		
		int maxNumOfTransitions = size * alphabetSize * size;
		int numOfTransitions =
					(int) Math.round(internalTransitionDensity * maxNumOfTransitions);
		if (numOfTransitions < size - 1)
			throw new IllegalArgumentException(
					"Not all states reachable with given transition density.");
		
		int numOfAccStates = (int) Math.round(acceptanceDensity * size);
		
		// ────────────────────────────────────────────────────────────────────
		// Create state and letter objects and store them in two lists.
		//
		List<String> num2State = new ArrayList<String>(size);
		for (int i = 0; i < size; ++i) {
			num2State.add("q" + i);
		}
		String initialState = num2State.get(0);  // q₀
		
		List<String> num2Letter = new ArrayList<String>(alphabetSize);
		for (int i = 0; i < alphabetSize; ++i) {
			num2Letter.add("a" + i);
		}
		
		// ────────────────────────────────────────────────────────────────────
		// Create the result automaton.
		// If both, callTransitionProbability and returnTransitionProbability 
		// are 0 we set callAlphabet and returnAlphabet to null.
		//
		StateFactory<String> stateFactory = new StringFactory();
		INestedWordAutomaton<String,String> result;
		if (isFiniteAutomaton) {
			result = new NestedWordAutomaton<String,String>(
					num2Letter, null, null,	stateFactory);			
		} else {
			result = new NestedWordAutomaton<String,String>(
					num2Letter, num2Letter, num2Letter,	stateFactory);						
		}
		
		// ────────────────────────────────────────────────────────────────────
		// Add the states to the result automaton.
		//
		List<String> shuffledStateList = new ArrayList<String>(num2State);
		Collections.shuffle(shuffledStateList, m_Random);
		// • Accepting states:
		for (int i = 0; i < numOfAccStates; ++i) {
			String state = shuffledStateList.get(i);
			if (state == initialState)
				result.addState(true, true, state);
			else
				result.addState(false, true, state);
		}
		// • Non-accepting states:
		for (int i = numOfAccStates; i < size; ++i) {
			String state = shuffledStateList.get(i);
			if (state == initialState)
				result.addState(true, false, state);
			else
				result.addState(false, false, state);
		}

/*
 * What follows is essentially an implementation of the approach described in
 * [1]. However, the transition function is not encoded as a bit-stream and the
 * transitions are numbered slightly differently.
 * 
 * TRANSITION NUMBERS
 * ──────────────────
 * Let n = |Q| be the number of states and k = |Σ| the number of symbols. Then
 * there are n²k possible transitions. Every transition gets assigned a unique
 * number between 0 and n²k−1.
 * The number assigned to the transition ⟨qₚ,aₓ⟩ ↦ qₛ is
 *   p·(kn) + x·(n) + s .
 *      
 *   0 ···                                                             ··· n²k−1
 * ┏━━━━┳╺╺╺╺┳━━━━┳━  ━┳━━━━┳╺╺╺╺┳━━━━┳━   ━┳━━━━┳╺╺╺╺┳━━━━┳━  ━┳━━━━┳╺╺╺╺┳━━━━┓
 * ┃ q₀ ┃ ·· ┃qₙ₋₁┃ ·· ┃ q₀ ┃ ·· ┃qₙ₋₁┃ ··· ┃ q₀ ┃ ·· ┃qₙ₋₁┃ ·· ┃ q₀ ┃ ·· ┃qₙ₋₁┃
 * ┗━━━━┻╸╸╸╸┻━━━━┻━  ━┻━━━━┻╸╸╸╸┻━━━━┻━   ━┻━━━━┻╸╸╸╸┻━━━━┻━  ━┻━━━━┻╸╸╸╸┻━━━━┛
 * ╰───── a₀ ─────╯    ╰──── aₖ₋₁ ────╯     ╰───── a₀ ─────╯    ╰──── aₖ₋₁ ────╯
 * │                                  │ ··· │                                  │
 * ╰─────────────── q₀ ───────────────╯     ╰────────────── qₙ₋₁ ──────────────╯
 * 
 * [1] Marco Almeida, Nelma Moreira and Rogério Reis,
 *     “On the Performance of Automata Minimization Algorithms” (2008),
 *     Section 4 (“Random Automata Generation”).
 */
		
		// ────────────────────────────────────────────────────────────────────
		// Add n−1 transitions s.t. every state becomes reachable from q₀.
		//
		List<Integer> reachedStateNbs = new ArrayList<Integer>(size);
		reachedStateNbs.add(0);  // [q₀]
		
		// Q \{q₀} in random order:
		List<Integer> shuffledStateNbList = new ArrayList<Integer>(size - 1);
		for (int stateNb = 1; stateNb < size; ++stateNb) {
			shuffledStateNbList.add(stateNb);
		}
		Collections.shuffle(shuffledStateNbList, m_Random);
		
		// Transition numbers that will not be used again:
		Set<Integer> usedTransitionNbs = new HashSet<Integer>(size - 1);
		
		for (int i = 0; i < shuffledStateNbList.size(); ++i) {
			int predStateNb =  // random reached state
					reachedStateNbs.get(m_Random.nextInt(reachedStateNbs.size()));
			int letterNb = m_Random.nextInt(alphabetSize);  // random letter
			int succStateNb = shuffledStateNbList.get(i);   // rd. isolated state
			reachedStateNbs.add(succStateNb);
			int transitionNb = predStateNb * alphabetSize * size
								+ letterNb * size + succStateNb;
			usedTransitionNbs.add(transitionNb);
			String predState = num2State.get(predStateNb);
			String letter = num2Letter.get(letterNb);
			String succState = num2State.get(succStateNb);
			result.addInternalTransition(predState, letter, succState);
		}
		
		// ────────────────────────────────────────────────────────────────────
		// Add further random transitions until the desired density is reached.
		//
		// Unused transition numbers in random order:
		List<Integer> shuffledTransitionNbList =
						new ArrayList<Integer>(maxNumOfTransitions - size + 1);
		for (int transNb = 0; transNb < maxNumOfTransitions; ++transNb) {
			if (!usedTransitionNbs.contains(transNb))
				shuffledTransitionNbList.add(transNb);	
		}
		Collections.shuffle(shuffledTransitionNbList, m_Random);
		
		int remainingNumOfTransitions = numOfTransitions - size + 1;
		for (int i = 0; i < remainingNumOfTransitions; ++i) {
			int transitionNb = shuffledTransitionNbList.get(i);
			int predStateNb = transitionNb / (alphabetSize * size);
			int letterNb = (transitionNb % (alphabetSize * size)) / size;
			int succStateNb = transitionNb % size;
			String predState = num2State.get(predStateNb);
			String letter = num2Letter.get(letterNb);
			String succState = num2State.get(succStateNb);
			result.addInternalTransition(predState, letter, succState);
		}
		// ────────────────────────────────────────────────────────────────────
		// add call transitions with probability callTransitionProbability
		
		if (!isFiniteAutomaton) {
			for (String pred : num2State) {
				for (String letter : num2Letter) {
					for (String succ : num2State) {
						if (m_Random.nextFloat() < callTransitionProbability) {
							result.addCallTransition(pred, letter, succ);
						}
					}
				}
			}
			
			for (String pred : num2State) {
				for (String hier : num2State) {
					for (String letter : num2Letter) {
						for (String succ : num2State) {
							if (m_Random.nextFloat() < returnTransitionProbability) {
								result.addReturnTransition(pred, hier, letter, succ);
							}
						}
					}
				}
			}
		}
		
		return result;
	}	
}