package de.uni_freiburg.informatik.ultimate.automata;

import java.io.File;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Collection;
import java.util.Date;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter.Labeling;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.GetRandomNestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeDfa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;

@Deprecated
public class ResultChecker<LETTER,STATE> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private static int resultCheckStackHeight = 0;
	public static final int maxResultCheckStackHeight = 1;
	
	public final static boolean m_InvariantCheck_DetComplementBuchi = false;
	
	public static boolean doingInvariantCheck() {
		return resultCheckStackHeight > 0;
	}


	
	
	
	public static boolean reduceBuchi(INestedWordAutomatonOldApi operand,
			INestedWordAutomatonOldApi result) throws AutomataLibraryException {
		if (resultCheckStackHeight >= maxResultCheckStackHeight)
			return true;
		resultCheckStackHeight++;
		s_Logger.debug("Testing correctness of reduceBuchi");
		
		INestedWordAutomatonOldApi minimizedOperand = (new MinimizeDfa(operand)).getResult();

		boolean correct = true;
		NestedLassoRun inOperandButNotInResultBuchi = nwaBuchiLanguageInclusion(minimizedOperand,result);
		if (inOperandButNotInResultBuchi != null) {
			s_Logger.error("Lasso word accepted by operand, but not by result: " + 
					inOperandButNotInResultBuchi.getNestedLassoWord());
			correct = false;
		}
		NestedLassoRun inResultButNotInOperatndBuchi = nwaBuchiLanguageInclusion(result,minimizedOperand);
		if (inResultButNotInOperatndBuchi != null) {
			s_Logger.error("Lasso word accepted by result, but not by operand: " + 
					inResultButNotInOperatndBuchi.getNestedLassoWord());
			correct = false;
		}

		s_Logger.debug("Finished testing correctness of reduceBuchi");
		resultCheckStackHeight--;
		return correct;
	}
	
	public static boolean buchiEmptiness(INestedWordAutomatonOldApi operand,
										 NestedLassoRun result) {
		if (resultCheckStackHeight >= maxResultCheckStackHeight) return true;
		resultCheckStackHeight++;
		s_Logger.info("Testing correctness of buchiEmptiness");

		boolean correct = true;
		if (result == null) {
			s_Logger.warn("No check for positive buchiEmptiness");
		} else {
			correct = (new BuchiAccepts(operand, result.getNestedLassoWord())).getResult();
		}

		s_Logger.info("Finished testing correctness of buchiEmptiness");
		resultCheckStackHeight--;
		return correct;
	}
	
	
	public static boolean buchiIntersect(INestedWordAutomatonOldApi operand1,
			INestedWordAutomatonOldApi operand2,
			INestedWordAutomatonOldApi result) {
		if (resultCheckStackHeight >= maxResultCheckStackHeight) return true;
		resultCheckStackHeight++;
		s_Logger.info("Testing correctness of buchiIntersect");

		boolean correct = true;
		s_Logger.warn("No test for buchiIntersection available yet");

		s_Logger.info("Finished testing correctness of buchiIntersect");
		resultCheckStackHeight--;
		return correct;
	}
	

	
	public static boolean buchiComplement(INestedWordAutomatonOldApi operand,
										  INestedWordAutomatonOldApi result) throws OperationCanceledException {
		if (resultCheckStackHeight >= maxResultCheckStackHeight) return true;
		resultCheckStackHeight++;
		s_Logger.info("Testing correctness of complementBuchi");
		
		int maxNumberOfStates = Math.max(operand.size(), result.size());
		boolean correct = true;
		for (int i=0; i<10; i++) {
			NestedWord stem = (new GetRandomNestedWord(operand, maxNumberOfStates)).getResult();
			NestedWord loop = (new GetRandomNestedWord(operand, maxNumberOfStates)).getResult();
			NestedLassoWord lasso = new NestedLassoWord(stem, loop);
			boolean operandAccepts = (new BuchiAccepts(operand, lasso)).getResult();
			boolean resultAccepts = (new BuchiAccepts(result, lasso)).getResult();
			if (operandAccepts ^ resultAccepts) {
				// check passed
			} else {
				correct = false;
				String message = "// Problem with lasso " + lasso.toString();
				writeToFileIfPreferred("FailedBuchiComplementCheck", message, operand);
				break;
			}
		}
		
//		INestedWordAutomaton intersection = (new Intersect(true, false, operand, result)).getResult();
//		NestedLassoRun ctx = new EmptinessCheck().getAcceptingNestedLassoRun(intersection);
//		boolean correct = (ctx == null);
//		assert (correct);
		
		s_Logger.info("Finished testing correctness of complementBuchi");
		resultCheckStackHeight--;
		return correct;
	}
	
	
	public static boolean buchiComplementSVW(INestedWordAutomatonOldApi operand,
			INestedWordAutomatonOldApi result) throws OperationCanceledException {
		if (resultCheckStackHeight >= maxResultCheckStackHeight) return true;
		resultCheckStackHeight++;
		s_Logger.info("Testing correctness of complementBuchiSVW");
		
		int maxNumberOfStates = Math.max(operand.size(), result.size());
		boolean correct = true;
		for (int i=0; i<10; i++) {
			NestedWord stem = (new GetRandomNestedWord(operand, maxNumberOfStates)).getResult();
			NestedWord loop = (new GetRandomNestedWord(operand, maxNumberOfStates)).getResult();
			NestedLassoWord lasso = new NestedLassoWord(stem, loop);

			boolean operandAccepts = (new BuchiAccepts(operand, lasso)).getResult();
			boolean resultAccepts = (new BuchiAccepts(operand, lasso)).getResult();
			if (operandAccepts ^ resultAccepts) {
				// ok
			} else {
				correct = false;
				break;
			}
		}


//		{
//			INestedWordAutomaton intersection = (new Intersect(true, false, operand, result)).getResult();
//			NestedLassoRun ctx = new EmptinessCheck().getAcceptingNestedLassoRun(intersection);
//			correct = (ctx == null);
//			assert (correct);
//		}
//		
//		{
//			INestedWordAutomaton operandComplement = (new BuchiComplementFKV(operand)).getResult();
//			INestedWordAutomaton resultComplement = (new BuchiComplementFKV(result)).getResult();
//			INestedWordAutomaton intersection = (new Intersect(true, false, operandComplement, resultComplement)).getResult();
//			NestedLassoRun ctx = new EmptinessCheck().getAcceptingNestedLassoRun(intersection);
//			correct = (ctx == null);
//			assert (correct);
//		}

		s_Logger.info("Finished testing correctness of complementBuchiSVW");
		resultCheckStackHeight--;
		return correct;
	}
	
	
	
	public static boolean petriNetJulian(INestedWordAutomatonOldApi op,
										 PetriNetJulian result) throws AutomataLibraryException {
		if (resultCheckStackHeight >= maxResultCheckStackHeight) return true;
		resultCheckStackHeight++;
		s_Logger.info("Testing correctness of PetriNetJulian constructor");

		INestedWordAutomatonOldApi resultAutomata = 
							(new PetriNet2FiniteAutomaton(result)).getResult();
		boolean correct = true;
		correct &= (nwaLanguageInclusion(resultAutomata,op,op.getStateFactory()) == null);
		correct &= (nwaLanguageInclusion(op,resultAutomata,op.getStateFactory()) == null);

		s_Logger.info("Finished testing correctness of PetriNetJulian constructor");
		resultCheckStackHeight--;
		return correct;
	}
	
	

	

	public static boolean petriNetLanguageEquivalence(PetriNetJulian net1, PetriNetJulian net2) throws AutomataLibraryException {
		if (resultCheckStackHeight >= maxResultCheckStackHeight) return true;
		resultCheckStackHeight++;
		s_Logger.info("Testing Petri net language equivalence");
		INestedWordAutomatonOldApi finAuto1 = (new PetriNet2FiniteAutomaton(net1)).getResult();
		INestedWordAutomatonOldApi finAuto2 = (new PetriNet2FiniteAutomaton(net2)).getResult();
		NestedRun subsetCounterex = nwaLanguageInclusion(finAuto1, finAuto2, net1.getStateFactory());
		boolean subset = subsetCounterex == null;
		if (!subset) {
			s_Logger.error("Only accepted by first: " + subsetCounterex.getWord());
		}
		NestedRun supersetCounterex = nwaLanguageInclusion(finAuto2, finAuto1, net1.getStateFactory());
		boolean superset = supersetCounterex == null;
		if (!superset) {
			s_Logger.error("Only accepted by second: " + supersetCounterex.getWord());
		}
		boolean result = subset && superset;
		s_Logger.info("Finished Petri net language equivalence");
		resultCheckStackHeight--;
		return result;
	}
	
	
	public static <E> boolean isSubset(Collection<E> lhs, Collection<E> rhs) {
		for (E elem : lhs) {
			if (!rhs.contains(elem)) {
				return false;
			}
		}
		return true;
	}


	public static <LETTER,STATE> NestedRun nwaLanguageInclusion(INestedWordAutomatonOldApi nwa1, INestedWordAutomatonOldApi nwa2, StateFactory stateFactory) throws AutomataLibraryException {
		IStateDeterminizer stateDeterminizer = new PowersetDeterminizer<LETTER,STATE>(nwa2, true);
		INestedWordAutomatonOldApi nwa1MinusNwa2 = (new DifferenceDD(nwa1, nwa2, stateDeterminizer, stateFactory, false, false)).getResult();
		NestedRun inNwa1ButNotInNwa2 = (new IsEmpty(nwa1MinusNwa2)).getNestedRun();
		return inNwa1ButNotInNwa2;
//		if (inNwa1ButNotInNwa2 != null) {
//			s_Logger.error("Word accepted by nwa1, but not by nwa2: " + 
//					inNwa1ButNotInNwa2.getWord());
//			correct = false;
//		}
	}
	
	public static <LETTER, STATE> INestedWordAutomatonOldApi<LETTER, STATE> getOldApiNwa(
			INestedWordAutomatonSimple<LETTER, STATE> nwa)
			throws OperationCanceledException {
		if (nwa instanceof INestedWordAutomatonOldApi) {
			return (INestedWordAutomatonOldApi<LETTER, STATE>) nwa;
		} else {
			return (new RemoveUnreachable<LETTER, STATE>(nwa)).getResult();
		}
	}
	
	private static NestedLassoRun nwaBuchiLanguageInclusion(INestedWordAutomatonOldApi nwa1, INestedWordAutomatonOldApi nwa2) throws AutomataLibraryException {
		return (new BuchiIsIncluded(nwa1, nwa2)).getCounterexample();
	}
	
	
    private static String getDateTime() {
        DateFormat dateFormat = new SimpleDateFormat("yyyyMMddHHmmss");
        Date date = new Date();
        return dateFormat.format(date);
    }
    
    public static void writeToFileIfPreferred(String filenamePrefix, String message, IAutomaton... automata) {
		IScopeContext scope = InstanceScope.INSTANCE;
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		boolean writeToFile = prefs.getBoolean(PreferenceInitializer.Name_Write);
		if (writeToFile) {
			String directory = prefs.getString(PreferenceInitializer.Name_Path); 
			String filename = directory + File.separator+filenamePrefix + getDateTime() + ".fat";
			new AtsDefinitionPrinter(filenamePrefix, filename, Labeling.QUOTED, message, automata);
		}
    }
    
	public static <LETTER,STATE> NestedLassoWord<LETTER> getRandomNestedLassoWord(INestedWordAutomatonSimple<LETTER, STATE> automaton, int size) throws OperationCanceledException {
		NestedWord<LETTER> stem = (new GetRandomNestedWord<LETTER, STATE>(automaton, size)).getResult();
		NestedWord<LETTER> loop = (new GetRandomNestedWord<LETTER, STATE>(automaton, size)).getResult();
		return new NestedLassoWord<LETTER>(stem, loop);
	}
    
	
}
