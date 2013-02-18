package local.stalin.automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.StateNameFactory;
import local.stalin.automata.nwalibrary.buchiNwa.NestedLassoRun;
import local.stalin.automata.nwalibrary.buchiNwa.NestedLassoWord;
import local.stalin.automata.parser.astAnnotations.AutomatonNameExpression;
import local.stalin.automata.parser.astAnnotations.NestedLassoWordTestCase;
import local.stalin.automata.parser.astAnnotations.NestedWordTestCase;
import local.stalin.automata.parser.astAnnotations.NoWordTestCase;
import local.stalin.automata.parser.astAnnotations.OperationExpression;
import local.stalin.automata.parser.astAnnotations.StartNode;
import local.stalin.automata.parser.astAnnotations.SymbolAtCallPosition;
import local.stalin.automata.parser.astAnnotations.SymbolAtInternalPosition;
import local.stalin.automata.parser.astAnnotations.SymbolAtReturnPosition;
import local.stalin.automata.parser.astAnnotations.TestFile;
import local.stalin.automata.parser.astAnnotations.nwa.CallTransition;
import local.stalin.automata.parser.astAnnotations.nwa.InternalTransition;
import local.stalin.automata.parser.astAnnotations.nwa.NwaDefinition;
import local.stalin.automata.parser.astAnnotations.nwa.ReturnTransition;
import local.stalin.automata.parser.astAnnotations.petrinet.PetriNetJanDefinition;
import local.stalin.automata.parser.astAnnotations.petrinet.PetriNetJulianDefinition;
import local.stalin.automata.parser.astAnnotations.petrinet.TransitionDefinition;
import local.stalin.automata.petrinet.jan.IOccurrenceNet;
import local.stalin.automata.petrinet.jan.IPetriNetJan;
import local.stalin.automata.petrinet.IPetriNet;
import local.stalin.automata.petrinet.Place;
import local.stalin.automata.petrinet.jan.OperationsWithTests;
import local.stalin.automata.petrinet.jan.PetriNet;
import local.stalin.automata.petrinet.jan.PetriNet2FiniteAutomaton;
import local.stalin.automata.petrinet.jan.SelfloopIntersection;
import local.stalin.automata.petrinet.jan.Transition;
import local.stalin.automata.petrinet.julian.DifferenceBlackAndWhite;
import local.stalin.automata.petrinet.julian.PetriNetJulian;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IAnnotations;
import local.stalin.model.INode;

import org.apache.log4j.Logger;

 /**
  * Class that contains methods to execute tests provided by the AutomataParser
  * plugin. The AutomataParser provides tests as a STALIN AST.
  * The constructor should be called on the root Node of the STALIN AST.
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
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
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
	 * @param Root node of the STALIN Ast of an automaton test file
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
			else if (tfChildAnnot instanceof PetriNetJanDefinition){
				parsePetriNetJanDefinition(tfChild);
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
		if (!m_Testcases.isEmpty()) {
			boolean results = true;
			for (INode testCaseNode : m_Testcases) {
				boolean result = parseTestCase(testCaseNode);
				results = results && result;
			}
			if (results) {
				s_Logger.info("All testcases passed.");
			}
			else {
				s_Logger.info("Some testcases failed.");
			}
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
	 */
	private boolean parseTestCase(INode testCaseNode) {
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
	 */
	@SuppressWarnings("unchecked")
	private boolean executeNoWordTestCase(String operation,
			AutomatonWithExpression autom) {
		assert(autom.getAutomaton() != null);
		
		if (operation.equals("Print")) {
			if (this.m_PrintAutomaton != null) {
				s_Logger.error("Can print only one automaton");
				throw new IllegalArgumentException("Fat file contains errors");
			}
			else {
				this.m_PrintAutomaton = autom.getAutomaton();
				s_Logger.info("Printing automaton " + autom.getExpression());
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
			else if (autom.getAutomaton() instanceof IPetriNetJan) {
				// @Jan execution of you code is commissioned here (empty test)
				PetriNet<String,String> petriNet = 
					(PetriNet<String,String>) autom.getAutomaton();
//				NestedWord<String> word = petriNet.getAcceptedWord();
				if (useNwaWithTests) {
					NestedRun run = (new OperationsWithTests()).getAcceptingRun(petriNet);
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
				List<Collection<Place<String, String>>> word = 
					petriNet.getAcceptedRun();
				if(word == null)
				{
					s_Logger.info("The petri net " + autom.getExpression() + 
					"  has no accepting run");
					return true;
				}
				else {
					s_Logger.info("The petri   " + autom.getExpression() +
							" has an accepting run, for example:  " + 
							word.toString());
					return false;			
				}
				////////////////////////////////////////////////////////////
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
					nwa.getAcceptingNestedLassoRun();
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
					local.stalin.automata.parser.astAnnotations.NestedWord);
		
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
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) autom.getAutomaton();
				if(nwa.accepts(nlw))
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
	 */
	private AutomatonWithExpression parseExpression(INode nwaNode) {
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
			return executeAutomatonOperation(operation, operands);
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
	 */
	private AutomatonWithExpression executeAutomatonOperation(
			String operation,
			List<AutomatonWithExpression> operands) 
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
	 */
	@SuppressWarnings("unchecked")
	private Object executeAutomatonOperation(
			String operation,
			List<Object> operands) {
		
		if (operation.equals("intersect")){
			if (operands.size() != 2) {
				s_Logger.error("intersect requires two operands");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton && 
					operands.get(1) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa0 = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				NestedWordAutomaton<String,String> nwa1 = 
					(NestedWordAutomaton<String,String>) operands.get(1);
				return nwa0.intersect(nwa1);
			}
//			else if (operands.get(0) instanceof PetriNet && 
//					operands.get(1) instanceof NestedWordAutomaton) {
//				//////////TODO @Jan execution of you code is commissioned here (intersect)
//				PetriNet<String,String> petriNet = 
//					(PetriNet<String,String>) operands.get(0);
//				NestedWordAutomaton<String,String> nwa = 
//					(NestedWordAutomaton<String,String>) operands.get(1);
//				return petriNet.intersect(nwa);
//				//////////////////////////////////////////////////////////
//			}
			else {
				s_Logger.error("intersection only applicable to two NWAs or" +
						" one petri net and one NWA");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("determinize")){
			if (operands.size() != 1) {
				s_Logger.error("determinize requires one operand");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				return nwa.determinize();
			}
			else {
				s_Logger.error("determinization only applicable NWA");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("complement")){
			if (operands.size() != 1) {
				s_Logger.error("complement requires one operand");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				return nwa.complement();
			}
			else {
				s_Logger.error("determinization only applicable NWA");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("difference")){
			if (operands.size() != 2) {
				s_Logger.error("difference requires two operands");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton && 
					operands.get(1) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa0 = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				NestedWordAutomaton<String,String> nwa1 = 
					(NestedWordAutomaton<String,String>) operands.get(1);
				return nwa0.difference(nwa1);
			}
			else {
				s_Logger.error("difference only applicable to NWAs");
				throw new IllegalArgumentException();
			}
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
				return nwa0.getConcurrentProduct(nwa1);
			}
			else {
				s_Logger.error("Operation" + operation + "only applicable" +
						" to NWAs");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("concurrentProduct")){
			if (operands.size() != 2) {
				s_Logger.error("concurrentProduct requires two operands");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof IPetriNetJan && 
					operands.get(1) instanceof NestedWordAutomaton) {
				PetriNet<String,String> net = 
					(PetriNet<String,String>) operands.get(0);
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(1);
				if (useNwaWithTests) {
					net = (new OperationsWithTests<String,String>()).
													concurrentProduct(net,nwa);
				}
				else {
					net = net.concurrentProduct(nwa);
				}
				return net;
			}
			else {
				s_Logger.error("concurrentProduct only applicable to NWAs");
				throw new IllegalArgumentException();
			}
		}
		else if (operation.equals("prefixProduct")){
			if (operands.size() != 2) {
				s_Logger.error("prefixProduct requires two operands");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof PetriNetJulian && 
					operands.get(1) instanceof NestedWordAutomaton) {
				PetriNetJulian<String,String> net = 
					(PetriNetJulian<String,String>) operands.get(0);
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(1);
				return net.prefixProduct(net, nwa);
			}
			else {
				s_Logger.error("prefixProduct only applicable to PetriNet" +
						" and nwa");
				throw new IllegalArgumentException();
			}
		}
		else if (operation.equals("selfloopIntersect")){
			if (operands.size() != 2) {
				s_Logger.error("selfloopIntersect requires two operands");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof IPetriNetJan && 
					operands.get(1) instanceof NestedWordAutomaton) {
				PetriNet<String,String> net = 
					(PetriNet<String,String>) operands.get(0);
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(1);
				if (useNwaWithTests) {
					return (new OperationsWithTests<String,String>()).
						selfloopIntersection(net, nwa);
				}
				else {
					return (new SelfloopIntersection<String,String>(net, nwa)).
						getResult();
				}
			}
			else {
				s_Logger.error("concurrentProduct only applicable to NWAs");
				throw new IllegalArgumentException();
			}
		}
		else if (operation.equals("differenceBlackAndWhite")){
			if (operands.size() != 2) {
				s_Logger.error("selfloopIntersect requires two operands");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof PetriNetJulian && 
					operands.get(1) instanceof NestedWordAutomaton) {
				PetriNetJulian<String,String> net = 
					(PetriNetJulian<String,String>) operands.get(0);
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(1);
				return net.differenceBlackAndWhite(net, nwa);
			}
			else {
				s_Logger.error("DifferenceBlackAndWhite only applicable to NWAs");
				throw new IllegalArgumentException();
			}
		}
		else if (operation.equals("petriNet")){
			if (operands.size() != 1) {
				s_Logger.error("operation petri requires one argument");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				PetriNet net;
				if (useNwaWithTests) {
					net = (new OperationsWithTests<String,String>()).
													concurrentProduct(nwa);
				}
				else {
					net = new PetriNet(nwa, new StateNameFactory());
				}
				s_Logger.debug("Casted PetriNet:" + net);
				return net;

			}
			else {
				s_Logger.error("concurrentProduct only applicable to NWAs");
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
			if (operands.size() != 1) {
				s_Logger.error("finitePrefix requires one operand");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof IPetriNetJan) {
				IPetriNetJan<String,String> net = 
					(IPetriNetJan<String,String>) operands.get(0);
				IOccurrenceNet<String,String> occurenceNet =  
											net.getFinitePrefix();
				return occurenceNet;
			}
			else {
				s_Logger.error("finitePrefix only applicable to Petri Net");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("finiteAutomaton")){
			if (operands.size() != 1) {
				s_Logger.error("operation finiteAutomaton requires exactly" +
						" one operand");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof IPetriNet) {
				IPetriNet<String,String> net = 
					(IPetriNet<String,String>) operands.get(0);
				return (new PetriNet2FiniteAutomaton<String,String>(net))
																.getResult(); 
			}
			else {
				s_Logger.error("operation finiteAutomaton only applicable" +
						" to Petri Net");
				throw new IllegalArgumentException();
			}
		}

		
		else if (operation.equals("downsize")){
			if (operands.size() != 1) {
				s_Logger.error("downsize requires exactly one operand");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				nwa.downsize();
				return nwa;
			}
			else {
				s_Logger.error("downsize only applicable for NWA");
				throw new IllegalArgumentException();
			}
		}
		
		else if (operation.equals("singleEntryNwa")){
			if (operands.size() != 1) {
				s_Logger.error("singleEntryNwa requires exactly one operand");
				throw new IllegalArgumentException();
			}
			if (operands.get(0) instanceof NestedWordAutomaton) {
				NestedWordAutomaton<String,String> nwa = 
					(NestedWordAutomaton<String,String>) operands.get(0);
				return nwa.constructSingleEntryNwa(nwa);
			}
			else {
				s_Logger.error("singleEntryNwa only applicable for NWA");
				throw new IllegalArgumentException();
			}
		}
	
		else {
			s_Logger.error("Operation " + operation + " not defined");
			throw new IllegalArgumentException();
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
				new StateNameFactory());

		initialStatesValid(aDef.getInitialStates(),aDef.getStates());
		finalStatesValid(aDef.getInitialStates(),aDef.getStates());
		Map<String,IState<String,String>> name2state =
			new HashMap<String,IState<String,String>>();
		for (String name : aDef.getStates()) {
			boolean isInitial = aDef.getInitialStates().contains(name);
			boolean isFinal = aDef.getFinalStates().contains(name);
			IState<String,String> state= nwa.addState(isInitial, isFinal, name);
			name2state.put(name, state);
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
			                   Map<String,IState<String,String>> name2states ) {
		IAnnotations transition = 
			transitionNode.getPayload().getAnnotations().get("Automata Parser");
		if (transition instanceof InternalTransition) {
			InternalTransition iTrans = (InternalTransition) transition;
			String predName = iTrans.getM_Predecessor();
			String succName = iTrans.getM_Successor();
			String symbol = iTrans.getM_Symbol();
			isInInternalAlphabet(symbol, nwa);
			IState<String,String> pred = name2states.get(predName);
			isInStatest(pred, nwa);
			IState<String,String> succ = name2states.get(succName);
			isInStatest(succ, nwa);
			nwa.addInternalTransition(pred, symbol, succ);
		}
		else if (transition instanceof CallTransition) {
			CallTransition iTrans = (CallTransition) transition;
			String predName = iTrans.getPredecessor();
			String succName = iTrans.getSuccessor();
			String symbol = iTrans.getSymbol();
			isInCallAlphabet(symbol, nwa);
			IState<String,String> pred = name2states.get(predName);
			isInStatest(pred, nwa);
			IState<String,String> succ = name2states.get(succName);
			isInStatest(succ, nwa);
			nwa.addCallTransition(pred, symbol, succ);
		}
		else if (transition instanceof ReturnTransition) {
			ReturnTransition iTrans = (ReturnTransition) transition;
			String predName = iTrans.getM_Predecessor();
			String succName = iTrans.getM_Successor();
			String callPredName = iTrans.getM_CallPredecessor();
			String symbol = iTrans.getM_Symbol();
			isInReturnAlphabet(symbol, nwa);
			IState<String,String> pred = name2states.get(predName);
			isInStatest(pred, nwa);
			IState<String,String> succ = name2states.get(succName);
			isInStatest(succ, nwa);
			IState<String,String> callPred = name2states.get(callPredName);
			isInStatest(callPred, nwa);
			nwa.addReturnTransition(pred, callPred, symbol, succ);
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
	
	private boolean isInStatest(IState<String,String> state,
			INestedWordAutomaton<String,String>nwa) {
		Collection<IState<String, String>> states = nwa.getAllStates();
		if (states.contains(state)) {
			return true;
		}
		else {
			s_Logger.error("State "+ state + " not contained in set of states");
			throw new IllegalArgumentException("Fat file contains errors");
		}
	}
	
	
	

	private void parsePetriNetJulianDefinition(INode tfChild) {
		IAnnotations automatonDefinition = 
			tfChild.getPayload().getAnnotations().get("Automata Parser");
		PetriNetJulianDefinition netDef = 
			(PetriNetJulianDefinition) automatonDefinition;
		
		PetriNetJulian<String,String> net = 
			new PetriNetJulian<String, String>(netDef.getAlphabet(), 
											   new StateNameFactory(),
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
	
	
	
	/**
	 * Constructs a PetriNet given a net defined by the abstract
	 * syntax tree and adds the net to the map nwas.
	 */
	private void parsePetriNetJanDefinition(INode tfChild) {
		//get the description of the petri net
		IAnnotations petriNetDefinition = 
			tfChild.getPayload().getAnnotations().get("Automata Parser");
		PetriNetJanDefinition nDef = (PetriNetJanDefinition) petriNetDefinition;
		
		//create a new instance of a petri net
		IPetriNetJan<String,String> net = new PetriNet<String,String>(nDef.getAlphabet(), new StateNameFactory());

		//validate initial marking and accepting markings 
		assert(initialMarkingValid(nDef.getInitialMarking(),nDef.getPlaces())) : "initial arking invalid";
		assert(acceptingMarkingsValid(nDef.getAcceptingMarkings(),nDef.getPlaces())) : "accepting markings invalid";

		//add the places
		Map<String,Place<String,String>> name2place =
			new HashMap<String,Place<String,String>>();
		for (String name : nDef.getPlaces()) {
			Place<String,String> place = net.addPlace(name);
			name2place.put(name, place);
		}

		//add the transitions and the pre- and successor references to places and transitions
		for (INode transitionNode : tfChild.getOutgoingNodes()) {
			addTransition(transitionNode, net, name2place);
		}
		
		//create and set the collections for initial marking
		HashSet<Place<String, String>> initialMarking = new HashSet<Place<String, String>>();
		for(String content : nDef.getInitialMarking())
			initialMarking.add(name2place.get(content));
		net.setInitialMarking(initialMarking);
		
		//create and set the collections for accepting markings
		HashSet<Collection<Place<String,String>>> acceptingMarkings = new HashSet<Collection<Place<String, String>>>();
		HashSet<Place<String,String>> marking;// = new HashSet<Place<String,String>>();
		for(ArrayList<String> currentMarking : nDef.getAcceptingMarkings()){
			marking = new HashSet<Place<String,String>>();
			for(String content : currentMarking)
				marking.add(name2place.get(content));
			acceptingMarkings.add(marking);
		}	
		net.setAcceptingMarkings(acceptingMarkings);


		s_Logger.info("Successfully parsed the petri net " + nDef.getName());
//		s_Logger.debug(net);
		m_Automata.put(nDef.getName(), net);
	}
	
	private boolean initialMarkingValid(ArrayList<String> initialMarking,
			ArrayList<String> places) {
		for (String place : initialMarking) {
			if (!places.contains(place)) {
				s_Logger.error("Place " + place + " from the initial marking not contained in places.");
				throw new IllegalArgumentException("Fat file contains errors");
			}
		}
		return true;
	}
	
	private boolean acceptingMarkingsValid(ArrayList<ArrayList<String>> acceptingMarkings,
			ArrayList<String> places) {
		for (ArrayList<String> acceptingMarking : acceptingMarkings) {
			for(String place : acceptingMarking){
				if (!places.contains(place)) {
					s_Logger.error("Place " + place + " from the accepting marking " + acceptingMarking.toString() + " not contained in places.");
					throw new IllegalArgumentException("Fat file contains errors");
				}
			}
		}
		return true;
	}
	
	private void addTransition(INode transitionNode, IPetriNetJan<String,String> net, Map<String,Place<String,String>> name2String){
		
		local.stalin.automata.parser.astAnnotations.petrinet.TransitionDefinition	astTransition =
			(local.stalin.automata.parser.astAnnotations.petrinet.TransitionDefinition)transitionNode.getPayload().getAnnotations().get("Automata Parser");
		
		Transition<String,String> transition = new Transition<String,String>(astTransition.getSymbol());
		
		for(String predecessor : astTransition.getPredecessors())
			if(name2String.get(predecessor) != null)
				transition.addPredecessorPlace(name2String.get(predecessor));
		
		for(String successor : astTransition.getSuccessors())
			if(name2String.get(successor) != null)
				transition.addSuccessorPlace(name2String.get(successor));

		assert(net.getAlphabet().contains(transition.getSymbol()));
		
		net.addTransition(transition);
	}
	
	
}
