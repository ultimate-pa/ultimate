package de.uni_freiburg.informatik.ultimate.automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementRE;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementSVW;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.EmptinessCheck;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ComplementSadd;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Determinize;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DeterminizeLazyTest;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DeterminizeSadd;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DifferenceSadd;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.AbstractIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IntersectNodd;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.MinimizeDfa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.SenwaBuilder;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.SuperDifference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ReduceBuchi;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.AutomatonNameExpression;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.NestedLassoWordTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.NestedWordTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.NoWordTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.OperationExpression;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.StartNode;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.SymbolAtCallPosition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.SymbolAtInternalPosition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.SymbolAtReturnPosition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.TestFile;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.nwa.CallTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.nwa.InternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.nwa.NwaDefinition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.nwa.ReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.petrinet.PetriNetJanDefinition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.petrinet.PetriNetJulianDefinition;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.petrinet.TransitionDefinition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.DifferenceBlackAndWhite;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.FinitePrefix2PetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.order;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PrefixProduct;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.INode;

 /**
  * Class that contains methods to execute tests provided by the AutomataParser
  * plugin. The AutomataParser provides tests as a Ultimate AST.
  * The constructor should be called on the root Node of the Ultimate AST.
  * The constructor processes the tests in two stages.
  * Stage1: Read all automata definitions and testcases. Defined automaton are
  * build and made available via the map m_Automata, testcases are stored in the
  * list m_Testcases.
  * Stage2: The testcases are executed. Evaluation of tests is written to the
  * logger.
  * If the testcases define that an automaton should be printed, this automaton
  * is available via getPrintAutomaton().

  * @author heizmann@informatik.uni-freiburg.de
  */
public class TestFileExecutor {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	/**
	 * Set to true to enable additional tests
	 * TODO: Preference page for this.
	 */
	 boolean useNwaWithTests = true;
	
	/**
	 * Maps name of automaton to object that represents automaton  
	 */
	Map<String,Object> m_Automata = new HashMap<String,Object>();
	
	/**
	 * List of all testcases contained in testfile
	 */
	List<INode> m_Testcases = new LinkedList<INode>();
	
	/**
	 * Automaton that should be printed
	 */
	Object m_PrintAutomaton;
	

	
	/**
	 * @param Root node of the Ultimate Ast of an automaton test file
	 */
	public TestFileExecutor(INode node) {
		IAnnotations startAnnot = 
			node.getPayload().getAnnotations().get("Automata Parser");
		assert (startAnnot instanceof StartNode);
		List<INode> StartChildren = node.getOutgoingNodes();
		assert StartChildren.size()==1;
		INode testFile = StartChildren.get(0);
		IAnnotations testFileAnnot = 
			testFile.getPayload().getAnnotations().get("Automata Parser");
		assert (testFileAnnot instanceof TestFile);
		List<INode> testFileChildren = testFile.getOutgoingNodes();
		for (INode tfChild : testFileChildren) {
			IAnnotations tfChildAnnot = 
				tfChild.getPayload().getAnnotations().get("Automata Parser");
			if (tfChildAnnot instanceof NwaDefinition) {
				parseAutomatonDefinition(tfChild);
			}
			else if (tfChildAnnot instanceof PetriNetJulianDefinition){
				parsePetriNetJulianDefinition(tfChild);
			}
			else if (tfChildAnnot instanceof NestedWordTestCase) {
				m_Testcases.add(tfChild);
			}
			else if (tfChildAnnot instanceof NestedLassoWordTestCase) {
				m_Testcases.add(tfChild);
			}
			else if (tfChildAnnot instanceof NoWordTestCase) {
				m_Testcases.add(tfChild);
			}
			else {
				throw new IllegalArgumentException();
			}
		}
		try {
			if (!m_Testcases.isEmpty()) {
				boolean results = true;
				for (INode testCaseNode : m_Testcases) {
					boolean result;

					result = parseTestCase(testCaseNode);

					results = results && result;
				}
				if (results) {
					s_Logger.info("All testcases passed.");
				}
				else {
					s_Logger.info("Some testcases failed.");
				}
			}
		} catch (OperationCanceledException e) {
			s_Logger.info("Performing testcases was canceled.");
		}
	}
	
	/**
	 * 
	 * @return The (unique) automaton that is specified by the testfile to be
	 * printed. Is null if the testfile does not specify an automaton to be
	 * printed.  
	 */
	public Object getPrintAutomaton() {
		return m_PrintAutomaton;
	}

	
	/**
	 * Parse and execute TestCase defined by subtree of AST. Returns true if the
	 * test has passed. A detailed result is written to the logger.
	 * @throws OperationCanceledException 
	 */
	private boolean parseTestCase(INode testCaseNode) throws OperationCanceledException {
		IAnnotations testcase = 
			testCaseNode.getPayload().getAnnotations().get("Automata Parser");
		if (testcase instanceof NoWordTestCase) {
			NoWordTestCase nwtc = (NoWordTestCase) testcase;
			String operation = nwtc.getOperation();
			List<INode> testCaseChildren = testCaseNode.getOutgoingNodes();
			AutomatonWithExpression nwa;
			if (testCaseChildren.size() == 1) {
				nwa = parseExpression(testCaseChildren.get(0));
			}
			else {
				throw new IllegalArgumentException();
			}
			return executeNoWordTestCase(operation,nwa);
		}
		else if (testcase instanceof NestedLassoWordTestCase) {
			NestedLassoWordTestCase nlwtc = (NestedLassoWordTestCase) testcase;
			String operation = nlwtc.getOperation();
			List<INode> testCaseChildren = testCaseNode.getOutgoingNodes();
			AutomatonWithExpression nwa = parseExpression(testCaseChildren.get(0));
			NestedWord<String> stem = parseNestedWord(testCaseChildren.get(1));
			NestedWord<String> loop = parseNestedWord(testCaseChildren.get(2));
			return executeNestedLassoWordTestCase(operation,nwa,stem,loop);
		}
		else if (testcase instanceof NestedWordTestCase) {
			NestedWordTestCase nwtc = (NestedWordTestCase) testcase;
			String operation = nwtc.getOperation();
			List<INode> testCaseChildren = testCaseNode.getOutgoingNodes();
			AutomatonWithExpression nwa = parseExpression(testCaseChildren.get(0));
			NestedWord<String> nw = parseNestedWord(testCaseChildren.get(1));
			s_Logger.debug("Parsed nested word: " + nw);
			return executeNestedWordTestCase(operation,nwa,nw);
		}
		else {
			throw new IllegalArgumentException();
		}
	}
	
	
	
	
	/**
	 * Defines the execution of a test in which the testoperation is only
	 * applied to an automaton. 
	 * @param operation   Name of the test operation
	 * @param autom   automaton operand
	 * @return true if the test passed, false otherwise
	 * @throws OperationCanceledException 
	 */
	@SuppressWarnings("unchecked")
	private boolean executeNoWordTestCase(String operation,
			AutomatonWithExpression autom) throws OperationCanceledException {
		assert(autom.getAutomaton() != null);
		
		if (operation.equals("Print")) {
			if (this.m_PrintAutomaton != null) {
				s_Logger.error("Can print only one automaton");
				throw new IllegalArgumentException("Fat file contains errors");
			}
			else {
				this.m_PrintAutomaton = autom.getAutomaton();
//				this.m_PrintAutomaton = new NestedWordAutomaton<String, String>((NestedWordAutomaton<String, String>) autom.getAutomaton(), false, true);
				s_Logger.info("Printing automaton " + autom.getExpression());
//				new TestFileWriter<String, String>(autom.getAutomaton(), "TheDumpedAutomaton", TestFileWriter.Labeling.TOSTRING);
//				new PetruchioWrapper<String, String>((PetriNetJulian<String, String>) autom.getAutomaton()).writeToFile("test.spec");
				return true;
			}
		}
		

		else if (operation.equals("IsEmpty")) {
			if (autom.getAutomaton() instanceof INestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) autom.getAutomaton();
				NestedRun<String, String> nr = nwa.getAcceptingNestedRun();
				if(nr == null)
				{
					s_Logger.info("The NWA " + autom.getExpression() + 
						"  has no accepting run");
					return true;
				}
				else {
					s_Logger.info("The NWA   " + autom.getExpression() +
							" has an accepting run, for example:  " + 
							nr.toString());
					return false;			
				}
			}
			else if (autom.getAutomaton() instanceof PetriNetJulian) {
				PetriNetJulian<String,String> petriNet = 
					(PetriNetJulian<String,String>) autom.getAutomaton();
				IRun<String, String> run;
//				run = (new PetriNet2FiniteAutomaton<String,String>(petriNet)).
//						getResult().acceptingRun();
//				run = new EmptinessPetruchio<String,String>(petriNet).
//						getResult();
				PetriNetUnfolder<String,String> unf = 
						new PetriNetUnfolder<String, String>(petriNet, order.ERV, false, true);
				run = unf.getAcceptingRun();
				if(run == null)
				{
					s_Logger.info("The petri net " + autom.getExpression() + 
					"  has no accepting run");
					return true;
				}
				else {
					s_Logger.info("The petri   " + autom.getExpression() +
							" has an accepting run, for example:  " + 
							run.toString());
					return false;			
				}
			}
			else if (autom.getAutomaton() instanceof PetriNetJulian) {
				PetriNetJulian<String,String> petriNet = 
					(PetriNetJulian<String,String>) autom.getAutomaton();
				NestedRun<String,String> run = petriNet.getAcceptingNestedRun();
				if(run == null)
				{
					s_Logger.info("The petri net " + autom.getExpression() + 
					"  has no accepting run");
					return true;
				}
				else {
					s_Logger.info("The petri   " + autom.getExpression() +
							" has an accepting run, for example:  " + 
							run.toString());
					return false;			
				}
			}
			
			
			else {
				s_Logger.error("IsEmpty and IsNotEmpty can only be applied" +
						" to a nested word automaton or a petri net.");
				return false;
			}
		}
		else if (operation.equals("IsNotEmpty")) {
			return !executeNoWordTestCase("IsEmpty", autom);
		}
		

		else if (operation.equals("IsEmptyBuchi")) {
			if (autom.getAutomaton() instanceof INestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) autom.getAutomaton();
				NestedLassoRun<String, String> nlr = 
					new EmptinessCheck().getAcceptingNestedLassoRun(nwa);
				if(nlr == null)
				{
					s_Logger.info("The NWA " + autom.getExpression() + 
							"  has no accepting nested lasso run");
					return true;
				}
				else {
					s_Logger.info("The NWA   " + autom.getExpression() + 
							" has an accepting nested lasso run, for" +
							" example:  " + nlr.toString());
					return false;			
				}
			}
			else {
				s_Logger.error("IsEmptyBuchi and IsNotEmptyBuchi can only" +
						" be applied to a nested word automaton");
				return false;
			}
		}
		else if (operation.equals("IsNotEmptyBuchi")) {
			return !executeNoWordTestCase("IsEmptyBuchi", autom);
		}
			
			
		else {
			s_Logger.error("Test operation " + operation + " not supported.");
			throw new IllegalArgumentException();
		}
	}

	
	
	
	
	
	/**
	 * Defines the execution of a test in which the testoperation is applied
	 * to an automaton and a word. 
	 * @param operation Name of the testoperation
	 * @param autom automaton operand
	 * @param nw word operand
	 * @return true if the test passed, false otherwise
	 */
	@SuppressWarnings("unchecked")
	private boolean executeNestedWordTestCase(String operation,
			AutomatonWithExpression autom, NestedWord<String> nw) 
	{
		if (operation.equals("Accepts")) {
			if (autom.getAutomaton() instanceof INestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) autom.getAutomaton();
				if(nwa.accepts(nw))
				{
					s_Logger.info("The NWA " + autom.getExpression() + 
							" accepts  the nested word " + nw);
					return true;
				}
				else {
					s_Logger.info("The NWA " + autom.getExpression() + 
							" does not accept the nested word " + nw);
					return false;			
				}
			}
			else if (autom.getAutomaton() instanceof IPetriNet) {
				//////////@Jan execution of you code is commissioned here (accepts)
				IPetriNet<String,String> petriNet = 
					(IPetriNet<String,String>) autom.getAutomaton();
				if(petriNet.accepts(nw))
				{
					s_Logger.info("The PetriNet " + autom.getExpression() + 
							" accepts the word " + nw);
					return true;
				}
				else {
					s_Logger.info("The PetriNet " + autom.getExpression() + 
							" does not accept the word " + nw);
					return false;			
				}
				//////////////////////////////////////////////////////////////
			}
			else {
				s_Logger.error("Accepts and NotAccepts can only" +
						" be applied to a nested word automaton or a petri" +
						" net.");
				return false;
			}
		}
		else if (operation.equals("NotAccepts")) {
			return !executeNestedWordTestCase("Accepts", autom, nw);
		}
		else {
			s_Logger.error("Test operation " + operation + " not supported.");
			throw new IllegalArgumentException();
		}
	}
	

	private NestedWord<String> parseNestedWord(INode nwNode) {
		IAnnotations nwAnnot = 
			nwNode.getPayload().getAnnotations().get("Automata Parser");
		assert (nwAnnot instanceof 
					de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.NestedWord);
		
		String[] emptyWord = { };
		int[] emptyNestingRelation = { };
		NestedWord<String> nw = 
				new NestedWord<String>(emptyWord, emptyNestingRelation); 
		
		for (INode symbol : nwNode.getOutgoingNodes()) {
			IAnnotations symbolAnnot = 
				symbol.getPayload().getAnnotations().get("Automata Parser");
			if (symbolAnnot instanceof SymbolAtCallPosition) {
				String identifier = 
					((SymbolAtCallPosition) symbolAnnot).getIdentifier();
				String[] word = { identifier };
				int[] nestingRelation = { NestedWord.PLUS_INFINITY };
				NestedWord<String> oneSymbolWord = 
					new NestedWord<String>(word, nestingRelation);
				nw = nw.concatenate(oneSymbolWord);
			}
			else if (symbolAnnot instanceof SymbolAtInternalPosition) {
				String identifier = 
					((SymbolAtInternalPosition) symbolAnnot).getIdentifier();
				String[] word = { identifier };
				int[] nestingRelation = { NestedWord.INTERNAL_POSITION };
				NestedWord<String> oneSymbolWord = 
					new NestedWord<String>(word, nestingRelation);
				nw = nw.concatenate(oneSymbolWord);
			}
			else if (symbolAnnot instanceof SymbolAtReturnPosition) {
				String identifier = 
					((SymbolAtReturnPosition) symbolAnnot).getIdentifier();
				String[] word = { identifier };
				int[] nestingRelation = { NestedWord.MINUS_INFINITY };
				NestedWord<String> oneSymbolWord = 
					new NestedWord<String>(word, nestingRelation);
				nw = nw.concatenate(oneSymbolWord);
			}
		}
		return nw;	
	}


	/**
	 * Defines the execution of a test in which the testoperation is applied
	 * to an automaton and a lasso word. 
	 * @param operation   Name of the testoperation
	 * @param autom   automaton operand
	 * @param stem   stem of the nested lasso word operand 
	 * @param loop    loop of the nested lasso word operand
	 * @return true if the test passed, false otherwise
	 */
	@SuppressWarnings("unchecked")
	private boolean executeNestedLassoWordTestCase(String operation,
			AutomatonWithExpression autom,
			NestedWord<String> stem,
			NestedWord<String> loop) 
	{
		NestedLassoWord<String> nlw = new NestedLassoWord<String>(stem, loop);
		if (operation.equals("AcceptsBuchi")) {
			if (autom.getAutomaton() instanceof INestedWordAutomaton) {
				INestedWordAutomaton<String,String> nwa = 
					(INestedWordAutomaton<String,String>) autom.getAutomaton();
				if(new BuchiAccepts<String,String>(nwa,nlw).getResult())
				{
					s_Logger.info("The NWA " + autom.getExpression() +
							" accepts  the nested word " + nlw);
					return true;
				}
				else {
					s_Logger.info("The NWA " + autom.getExpression() +
							" does not accept  the nested word " + nlw);
					return false;			
				}
			}
			else {
				s_Logger.error("AcceptsBuchi and NotAcceptsBuchi can only" +
				" be applied to a nested word automaton");
				return false;
			}
		}
		else if (operation.equals("NotAcceptsBuchi")) {
			return !executeNestedLassoWordTestCase("AcceptsBuchi", autom,
																	stem,loop);
		}
		else {
			s_Logger.error("Test operation " + operation + " not supported.");
			throw new IllegalArgumentException("Unknown Testcase");
		}
	}
	
	
	


	
	
	
	
	/**
	 * Parse expression (which describes an automaton) defined by subtree of the
	 * AST.
	 * @return AutomatonWithExpression, a pair of Automaton described by the
	 * expression and a String representation of the expression. 
	 * @throws OperationCanceledException 
	 */
	private AutomatonWithExpression parseExpression(INode nwaNode) throws OperationCanceledException {
		IAnnotations nwa = 
			nwaNode.getPayload().getAnnotations().get("Automata Parser");
		if (nwa instanceof AutomatonNameExpression) {
			String automatonName = ((AutomatonNameExpression) nwa).getName();
			if (!m_Automata.containsKey(automatonName)) {
				s_Logger.error("Automaton " + automatonName + " used in" +
						" expression, but not defined."); 
			}
			return new AutomatonWithExpression(m_Automata.get(automatonName),
																automatonName);
		}
		else if (nwa instanceof OperationExpression) {
			OperationExpression operationAutomaton = 
				((OperationExpression) nwa);
			String operation = operationAutomaton.getOperation();
			List<AutomatonWithExpression> operands = 
				new LinkedList<AutomatonWithExpression>();
			for (INode nwaNodeChild : nwaNode.getOutgoingNodes()) {
				operands.add(parseExpression(nwaNodeChild));
			}
			return executeOperation(operation, operands);
		}
		else {
			throw new IllegalArgumentException();
		}
	}
	
	
	
	/**
	 * Executes an automaton operation on a list of NwaWithExpression Objects
	 * @param operation Name of the operation
	 * @param operands
	 * @return
	 * @throws OperationCanceledException 
	 */
	private AutomatonWithExpression executeOperation(
			String operation,
			List<AutomatonWithExpression> operands) throws OperationCanceledException 
	{
		String expression = operation + "(";
		List<Object> automata =	new LinkedList<Object>();
		for (AutomatonWithExpression operand : operands) {
			expression += " ";
			expression += operand.getExpression();
			automata.add(operand.getAutomaton());
		}
		expression += ")";
		return new AutomatonWithExpression(
				executeAutomatonOperation(operation, automata),
				expression);		
	}
	
	/**
	 * Pair that consists of
	 * <ul> 
	 * <li> an automaton
	 * <li> and an expression that defines this automaton.
	 * </ul>
	 * @author heizmann@informatik.uni-freiburg.de
	 */
	private class AutomatonWithExpression {
		private final Object automaton;
		private final String expression;
		public AutomatonWithExpression(Object automaton, String expression) {
			assert(automaton != null);
			assert(expression != null);
			this.automaton = automaton;
			this.expression = expression;
		}
		public Object getAutomaton() {
			return automaton;
		}
		public String getExpression() {
			return expression;
		}
	}
	

	
	/**
	 * Executes an automaton operation on a list of automata
	 * @param operation Name of the operation
	 * @param operands
	 * @return automaton constructed by operation
	 * @throws OperationCanceledException 
	 */
	@SuppressWarnings("unchecked")
	private Object executeAutomatonOperation(
			String operation,
			List<Object> operands) throws OperationCanceledException {
		
		for (Object o : operands) {
			if (o instanceof INestedWordAutomaton) {
				INestedWordAutomaton auto = (INestedWordAutomaton) o;
				ResultChecker.nwaInvarintChecks(auto);
			}
		}
		
		if (operation.equals("reachableStatesCopy")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return new ReachableStatesCopy(op0, false, false, false, false).getResult();
		}
		
		if (operation.equals("senwa")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return new SenwaBuilder(op0).getResult();
		}
		
		if (operation.equals("determinize")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new Determinize<String,String>(op0)).getResult();
		}
		
		if (operation.equals("determinizeSadd")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new DeterminizeSadd<String,String>(op0)).getResult();
		}
		
		if (operation.equals("determinizeLazyTest")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new DeterminizeLazyTest<String,String>(op0, new PowersetDeterminizer<String, String>(op0))).getResult();
		}

		if (operation.equals("complement")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new Complement(op0)).getResult();
		}
		
		if (operation.equals("complementSadd")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new ComplementSadd(op0)).getResult();
		}

		if (operation.equals("intersect")){
			checkOperands(operation, operands, -100, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			INestedWordAutomaton op1 = (INestedWordAutomaton) operands.get(1);
			return (new Intersect<String,String>(true, op0, op1)).getResult();
		}
		
		if (operation.equals("intersectNodd")){
			checkOperands(operation, operands, -100, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			INestedWordAutomaton op1 = (INestedWordAutomaton) operands.get(1);
			return (new IntersectNodd<String,String>(op0, op1)).getResult();
		}
		
		if (operation.equals("difference")){
			checkOperands(operation, operands, -100, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			INestedWordAutomaton op1 = (INestedWordAutomaton) operands.get(1);
			return (new Difference(op0, op1)).getResult();
		}
		
		if (operation.equals("differenceSenwa")){
			checkOperands(operation, operands, -100, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			INestedWordAutomaton op1 = (INestedWordAutomaton) operands.get(1);
			return (new DifferenceSenwa(op0, op1)).getResult();
		}
		
		if (operation.equals("superDifference")){
			checkOperands(operation, operands, -100, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			INestedWordAutomaton op1 = (INestedWordAutomaton) operands.get(1);
			AutomatonEpimorphism<String> epi =
					AutomatonEpimorphism.GetFromAutomatonLabels(op0, op1);
			return (new SuperDifference(op0, op1, epi, false)).getResult();
		}
		
		if (operation.equals("differenceSadd")){
			checkOperands(operation, operands, -100, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			INestedWordAutomaton op1 = (INestedWordAutomaton) operands.get(1);
			return (new DifferenceSadd(op0, op1)).getResult();
		}
		
		if (operation.equals("minimizeDFA")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new MinimizeDfa(op0)).getResult();
		}
		
		if (operation.equals("minimizeSevpa")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new MinimizeSevpa(op0)).getResult();
		}
		
		if (operation.equals("buchiReduce")) {
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			return (new ReduceBuchi(op0)).getResult();
		}
		
		if (operation.equals("buchiIntersect")){
			checkOperands(operation, operands, -100, -100);
			INestedWordAutomaton op0 = (INestedWordAutomaton) operands.get(0);
			INestedWordAutomaton op1 = (INestedWordAutomaton) operands.get(1);
			return (new Intersect(true, op0, op1)).getResult();
		}
		
		else if (operation.equals("buchiComplementFKV")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op = (INestedWordAutomaton) operands.get(0);
			return (new BuchiComplementFKV<String, String>(op)).getResult();
		}
		
		else if (operation.equals("buchiComplementSVW")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op = (INestedWordAutomaton) operands.get(0);
			return (new BuchiComplementSVW<String, String>(op)).getResult();
		}
		
		else if (operation.equals("buchiComplementDeterministic")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op = (INestedWordAutomaton) operands.get(0);
			return (new BuchiComplementDeterministic<String, String>(op)).getResult();
		}
		
		else if (operation.equals("buchiComplementRE")){
			checkOperands(operation, operands, -100);
			INestedWordAutomaton op = (INestedWordAutomaton) operands.get(0);
			return (new BuchiComplementRE<String, String>(op)).getResult();
		}
		
		else if (operation.equals("finiteAutomaton")){
			checkOperands(operation, operands, -110);
			IPetriNet op = (IPetriNet) operands.get(0);
			return (new PetriNet2FiniteAutomaton<String,String>(op)).getResult(); 
		}
		
		else if (operation.equals("prefixProduct")){
			checkOperands(operation, operands, -111, -101);
			PetriNetJulian op0 = (PetriNetJulian) operands.get(0);
			NestedWordAutomaton op1 = (NestedWordAutomaton) operands.get(1);
			return (new PrefixProduct<String, String>(op0, op1)).getResult();
		}
		
		else if (operation.equals("differenceBlackAndWhite")){
			checkOperands(operation, operands, -111, -101);
			PetriNetJulian op0 = (PetriNetJulian) operands.get(0);
			NestedWordAutomaton op1 = (NestedWordAutomaton) operands.get(1);
			return (new DifferenceBlackAndWhite<String, String>(op0, op1)).getResult();
		}
		
		else if (operation.equals("concurrentProductAutomaton")){
			if (operands.size() != 2) {
				s_Logger.error("Operation" + operation + 
						"requires exactly two operands");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton && 
					operands.get(1) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa0 = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				NestedWordAutomaton<String,String> nwa1 = 
					(NestedWordAutomaton<String,String>) operands.get(1);
				return nwa0.concurrentProduct(nwa1);
			}
			else {
				s_Logger.error("Operation" + operation + "only applicable" +
						" to NWAs");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("petriNetJulian")){
			if (operands.size() != 1) {
				s_Logger.error("operation petri requires one argument");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				IPetriNet net = new PetriNetJulian(nwa);
				return net;

			}
			else {
				s_Logger.error("petriNetJulian only applicable to NWAs");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("finitePrefix")){
			checkOperands(operation, operands, -111);
			if (operands.get(0) instanceof PetriNetJulian) {
				PetriNetJulian<String,String> net = 
						(PetriNetJulian<String,String>) operands.get(0);
					PetriNetUnfolder<String,String> unf = new PetriNetUnfolder<String, String>(net, order.ERV, true, false);
					return unf.getFinitePrefix();
				}
			else {
				s_Logger.error("finitePrefix only applicable to Petri Net");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("finitePrefix2PetriNet")){
			checkOperands(operation, operands, -112);
			if (operands.get(0) instanceof BranchingProcess) {
				BranchingProcess<String,String> bp = (BranchingProcess<String,String>) operands.get(0);
					FinitePrefix2PetriNet<String,String> fp2pn = new FinitePrefix2PetriNet<String, String>(bp);
					return fp2pn.getResult();
				}
			else {
				s_Logger.error("finitePrefix only applicable to Petri Net");
				throw new IllegalArgumentException();
			}
		}
		

		else {
			s_Logger.error("Operation " + operation + " not defined");
			throw new IllegalArgumentException("Operation not defined");
		}
		
	}
	

	
	
	/**
	 * Check if given operand have the type of the desired operands.
	 * Desired operand are encoded by ints
	 */
	private void checkOperands(String operation, List<Object> givenOperands,
												 int... desiredOperands) {
		if (givenOperands.size() != desiredOperands.length) {
			throw new IllegalArgumentException(operation + " requires " +
					desiredOperands.length + "operands");
		}
		for (int i=0; i<desiredOperands.length; i++) {
			switch (desiredOperands[i]) {
			case -100:
				if (!(givenOperands.get(i) instanceof INestedWordAutomaton)) {
					throw new IllegalArgumentException("Operand "+ i + 
							" of operation " + operation +
							"has to be an INestedWordAutomaton");
				}
				break;
			case -101:
				if (!(givenOperands.get(i) instanceof NestedWordAutomaton)) {
					throw new IllegalArgumentException("Operand "+ i + 
							" of operation " + operation +
							"has to be a NestedWordAutomaton");
				}
				break;
			case -110:
				if (!(givenOperands.get(i) instanceof IPetriNet)) {
					throw new IllegalArgumentException("Operand "+ i +
							" of operation " + operation +
							"has to be an IPetriNet");
				}
				break;
			case -111:
				if (!(givenOperands.get(i) instanceof PetriNetJulian)) {
					throw new IllegalArgumentException("Operand "+ i +
							" of operation " + operation +
							"has to be a PetriNetJulian");
				}
				break;
			case -112:
				if (!(givenOperands.get(i) instanceof BranchingProcess)) {
					throw new IllegalArgumentException("Operand "+ i +
							" of operation " + operation +
							"has to be a BranchingProcess");
				}
				break;

			default:
				break;
			}
		}
		
	}
	
	
	

	/**
	 * Constructs a NestedWordAutomaton given a nwa defined by the abstract
	 * syntax tree and adds the automaton to the map nwas.
	 */
	private void parseAutomatonDefinition(INode tfChild) {
		IAnnotations automatonDefinition = 
			tfChild.getPayload().getAnnotations().get("Automata Parser");
		NwaDefinition aDef = (NwaDefinition) automatonDefinition;
		
		NestedWordAutomaton<String,String> nwa = 
			new NestedWordAutomaton<String,String>(
				Collections.unmodifiableCollection(aDef.getInternalAlphabet()),
				Collections.unmodifiableCollection(aDef.getCallAlphabet()),
				Collections.unmodifiableCollection(aDef.getReturnAlphabet()),
				new StringFactory());
		
		// different equal strings should use same string object
		Map<String,String> name2state = new HashMap<String,String>();

		initialStatesValid(aDef.getInitialStates(),aDef.getStates());
		finalStatesValid(aDef.getInitialStates(),aDef.getStates());
		for (String name : aDef.getStates()) {
			boolean isInitial = aDef.getInitialStates().contains(name);
			boolean isFinal = aDef.getFinalStates().contains(name);
			nwa.addState(isInitial, isFinal, name);
			name2state.put(name,name);
		}
		List<INode> transitions = tfChild.getOutgoingNodes();
		for (INode transitionNode : transitions) {
			addTransition(transitionNode, nwa, name2state);
		}
		m_Automata.put(aDef.getName(), nwa);
	}
	
	private boolean initialStatesValid(ArrayList<String> initialStates,
			ArrayList<String> states) {
		for (String state : initialStates) {
			if (!states.contains(state)) {
				s_Logger.error("Initial state " + state + "not contained in" +
						" set of States");
				throw new IllegalArgumentException("Fat file contains errors");
			}
		}
		return true;
	}
	
	private boolean finalStatesValid(ArrayList<String> initialStates,
			ArrayList<String> states) {
		for (String state : initialStates) {
			if (!states.contains(state)) {
				s_Logger.error("Final state " + state + "not contained in" +
						" set of States");
				throw new IllegalArgumentException("Fat file contains errors");
			}
		}
		return true;
	}


	private void addTransition(INode transitionNode, 
			                   INestedWordAutomaton<String, String> nwa,
			                   Map<String,String> name2state) {
		IAnnotations transition = 
			transitionNode.getPayload().getAnnotations().get("Automata Parser");
		if (transition instanceof InternalTransition) {
			InternalTransition iTrans = (InternalTransition) transition;
			String predName = iTrans.getM_Predecessor();
			String pred = name2state.get(predName);
			String succName = iTrans.getM_Successor();
			String succ = name2state.get(succName);
			String symbol = iTrans.getM_Symbol();
			nwa.addInternalTransition(pred, symbol, succ);
		}
		else if (transition instanceof CallTransition) {
			CallTransition iTrans = (CallTransition) transition;
			String predName = iTrans.getPredecessor();
			String pred = name2state.get(predName);
			String succName = iTrans.getSuccessor();
			String succ = name2state.get(succName);
			String symbol = iTrans.getSymbol();
			isInCallAlphabet(symbol, nwa);
			nwa.addCallTransition(pred, symbol, succ);
		}
		else if (transition instanceof ReturnTransition) {
			ReturnTransition iTrans = (ReturnTransition) transition;
			String predName = iTrans.getM_Predecessor();
			String pred = name2state.get(predName);
			String succName = iTrans.getM_Successor();
			String succ = name2state.get(succName);
			String hierName = iTrans.getM_CallPredecessor();
			String hier = name2state.get(hierName);
			String symbol = iTrans.getM_Symbol();
			isInReturnAlphabet(symbol, nwa);
			nwa.addReturnTransition(pred, hier, symbol, succ);
		}
		else {
			throw new IllegalArgumentException();
		}
	}
	
	private boolean isInCallAlphabet(String symbol,
			INestedWordAutomaton<String,String>nwa) {
		if (nwa.getCallAlphabet().contains(symbol)) {
			return true;
		}
		else {
			s_Logger.error("Symbol "+ symbol + " not contained in call" +
					" alphabet.");
			throw new IllegalArgumentException("Fat file contains errors");
		}
	}
	
	private boolean isInInternalAlphabet(String symbol,
			INestedWordAutomaton<String,String>nwa) {
		if (nwa.getInternalAlphabet().contains(symbol)) {
			return true;
		}
		else {
			s_Logger.error("Symbol "+ symbol + " not contained in internal" +
					" alphabet");
			throw new IllegalArgumentException("Fat file contains errors");
		}
	}
	
	private boolean isInReturnAlphabet(String symbol,
			INestedWordAutomaton<String,String>nwa) {
		if (nwa.getReturnAlphabet().contains(symbol)) {
			return true;
		}
		else {
			s_Logger.error("Symbol "+ symbol + " not contained in return" +
					" alphabet");
			throw new IllegalArgumentException("Fat file contains errors");
		}
	}
	
//	private boolean isInStatest(IAuxiliaryStateContainer<String,String> state,
//			INestedWordAutomaton<String,String>nwa) {
//		Collection<IAuxiliaryStateContainer<String, String>> states = nwa.getAllStates();
//		if (states.contains(state)) {
//			return true;
//		}
//		else {
//			s_Logger.error("State "+ state + " not contained in set of states");
//			throw new IllegalArgumentException("Fat file contains errors");
//		}
//	}
	
	
	

	private void parsePetriNetJulianDefinition(INode tfChild) {
		IAnnotations automatonDefinition = 
			tfChild.getPayload().getAnnotations().get("Automata Parser");
		PetriNetJulianDefinition netDef = 
			(PetriNetJulianDefinition) automatonDefinition;
		
		PetriNetJulian<String,String> net = 
			new PetriNetJulian<String, String>(netDef.getAlphabet(), 
											   new StringFactory(),
											   false);
		Map<String,Place<String,String>> name2place = 
			new HashMap<String,Place<String,String>>();
		for (String name : netDef.getPlaces()) {
			boolean isInitial = netDef.getInitialMarking().contains(name);
			boolean isAccepting = netDef.getAcceptingPlaces().contains(name);
			Place<String,String> place = 
									net.addPlace(name, isInitial, isAccepting);
			name2place.put(name,place);
		}
		List<INode> transitions = tfChild.getOutgoingNodes();
		for (INode transitionNode : transitions) {
			addTransition(transitionNode, net, name2place);
		}
		m_Automata.put(netDef.getName(), net);
	}
	
	private void addTransition(INode transitionNode, 
			PetriNetJulian<String,String> net, 
			Map<String,Place<String,String>> name2place ) {
		IAnnotations transition = 
			transitionNode.getPayload().getAnnotations().get("Automata Parser");
		if (transition instanceof TransitionDefinition) {
			TransitionDefinition trans = (TransitionDefinition) transition;
			Collection<Place<String,String>> preds = 
				new ArrayList<Place<String,String>>();
			for (String name : trans.getPredecessors()) {
				if (!name2place.containsKey(name)) {
					throw new IllegalArgumentException("undefined place:" + name);
				}
				else {
					preds.add(name2place.get(name));
				}
			}
			Collection<Place<String,String>> succs = 
				new ArrayList<Place<String,String>>();
			for (String name : trans.getSuccessors()) {
				if (!name2place.containsKey(name)) {
					throw new IllegalArgumentException("undefined place:" + name);
				}
				else {
					succs.add(name2place.get(name));
				}
			}
			net.addTransition(trans.getSymbol(), preds, succs);
		}
		else {
			throw new IllegalArgumentException();
		}
	}
	
	
}
