package local.stalin.automata.parser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PushbackReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;

import local.TestGrammar.analysis.DepthFirstAdapter;
import local.TestGrammar.lexer.Lexer;
import local.TestGrammar.lexer.LexerException;
import local.TestGrammar.node.AAutomatonNameExpression;
import local.TestGrammar.node.ACallTaggedSymbol;
import local.TestGrammar.node.ACallTransition;
import local.TestGrammar.node.AInternalTaggedSymbol;
import local.TestGrammar.node.AInternalTransition;
import local.TestGrammar.node.AMarking;
import local.TestGrammar.node.ANestedLassoWordTestCase;
import local.TestGrammar.node.ANestedWord;
import local.TestGrammar.node.ANestedWordTestCase;
import local.TestGrammar.node.ANetTransition;
import local.TestGrammar.node.ANetjanAutomatonDefinition;
import local.TestGrammar.node.ANetjulianAutomatonDefinition;
import local.TestGrammar.node.ANoWordTestCase;
import local.TestGrammar.node.ANwaAutomatonDefinition;
import local.TestGrammar.node.AOperationExpression;
import local.TestGrammar.node.AReturnTaggedSymbol;
import local.TestGrammar.node.AReturnTransition;
import local.TestGrammar.node.ATestFile;
import local.TestGrammar.node.Node;
import local.TestGrammar.node.PAutomatonDefinition;
import local.TestGrammar.node.PCallTransition;
import local.TestGrammar.node.PExpression;
import local.TestGrammar.node.PInternalTransition;
import local.TestGrammar.node.PMarking;
import local.TestGrammar.node.PNestedWord;
import local.TestGrammar.node.PNetTransition;
import local.TestGrammar.node.PReturnTransition;
import local.TestGrammar.node.PTestCase;
import local.TestGrammar.node.Start;
import local.TestGrammar.node.Token;
import local.TestGrammar.parser.Parser;
import local.TestGrammar.parser.ParserException;
import local.stalin.automata.parser.astAnnotations.AutomatonNameExpression;
import local.stalin.automata.parser.astAnnotations.NestedLassoWordTestCase;
import local.stalin.automata.parser.astAnnotations.NestedWord;
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
import local.stalin.core.api.StalinServices;
import local.stalin.model.IAnnotations;
import local.stalin.model.INode;
import local.stalin.model.Payload;

import org.apache.log4j.Logger;

/**
 * The tree-structure is exact like the sablecc tree. 
 * In every node there is a key named "node" in the content 
 * which mappes to the type of the node. Further there are
 * some keys mapping to values (mostly Strings, but in some 
 * cases ArrayLists of Strings).
 * 
 * 
 * 
 * The types and values are:
 * 
 * 		KEY									MEANING / VALUE
 * - start								A START NODE
 * 
 * - print								A PRINT STATEMENT
 * 
 * - call								A CALL TRANSITION
 * 		- from								the state the transition comes from (String)
 * 		- to								the state the transition goes to (String)
 * 		- symbol							the symbol of the transition (String)
 * 	 
 * - return								A RETURN TRANSITION
 * 		- callfrom							the call-state which must be visited to do this transition (String)
 * 		- from								the state the transition comes from (String)
 * 		- to								the state the transition goes to (String)
 * 		- symbol							the symbol of the transition (String)
 * 
 * - internal							A INTERNAL TRANSITION
 * 		- from								the state the transition comes from (String)
 * 		- to								the state the transition goes to (String)
 * 		- symbol							the symbol of the transition (String)
 * 
 * - automaton							AN AUTOMATA
 * 		- name								name of the automata (String)
 * 		- call								call alphabet (ArrayList<String>)
 * 		- return							return alphabet (ArrayList<String>)
 * 		- internal							internal alphabet (ArraList<String>)
 * 		- initial							initial states (ArrayList<String>)
 * 		- states							normal states (ArrayList<String>)
 * 		- final								final states (ArrayList<String>)
 * 
 * - callsymbol						A CALL NESTED WORD SYMBOL
 * 		- callsymbol					the call symbol (String)
 * 
 * - returnsymbol					A RETRUN NESTED WORD SYMBOL
 * 		- returnsymbol					the return symbol (String)
 * 
 * - internalsymbol					A INTERNAL NESTED WORD SYMBOL
 * 		- internalsymbol				the internal symbol (String)
 * 
 * - accepttestcase						TESTCASEPART FOR "ACCEPTS"
 * 
 * - isemptytestcase					TESTCASEPART FOR "ISEMTPY"
 * 
 * - intersectjoinedautomaton			INTERSECT TWO AUTOMATON
 * 
 * - negatejoinedautomaton				NEGATE AN AUTOMATA
 * 
 * - determinizejoinedautomaton			DETERMINIZE AN AUTOMATA
 * 
 * - normaljoinedautomaton				A SINGLE AUTOMATA
 * 		- normaljoinedautomaton				the name of the automaton (String)
 */

/**
 * @author Jan Mortensen
 */
public class ASTBuilder extends DepthFirstAdapter{
	


	private Start sableccAST;
	private INode stalinAstRoot, subtree;
	private AutomataParser parser;
	private static Logger s_Logger = 
			StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	/**
	 * @author Jan Mortensen
	 */
	public ASTBuilder(AutomataParser parser){
		this.parser = parser;
	}

	/**
	 * @author Jan Mortensen
	 */	
	public boolean parse(File file){
		try{
			//Sablecc AST parsen
			Lexer lexer = new Lexer(new PushbackReader(new FileReader(file), 1024));
			Parser parser = new Parser(lexer);
			sableccAST = parser.parse();
			sableccAST.apply(this);
			s_Logger.info("File " + file.getName() + " sucessfully parsed.");
			return true;
		}
		catch(FileNotFoundException e){
			s_Logger.error("File " + file.getName() + " not found!");
			return false;
		}
		catch(IOException e){
			s_Logger.error("IOException!");
			return false;
		}
		catch(ParserException e){
			s_Logger.error("File not parsable!");
			s_Logger.error(e.getMessage());
			return false;
		}
		catch(LexerException e){
			s_Logger.error("File " + file.getName() + " not lexable!");
			s_Logger.error(e.getMessage());
			return false;
		}
		
	}
	
	public INode getAST(){
		return stalinAstRoot;
	}
	
	
	@SuppressWarnings("unchecked")
	public ArrayList<String> getArrayList(LinkedList tokenList) {
		ArrayList<String> al = new ArrayList<String>(tokenList.size());
		for(Object tId : tokenList){
			al.add( ((Token) tId).getText());
		}	
		return al;
	}
	
	
	@Override
	public void caseStart(Start node){
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		IAnnotations content = new StartNode();
		map.put(parser.getName(), content);
		Payload payload = new Payload(null,"Start");
		payload.setAnnotations(map);
		stalinAstRoot = new AutomataASTNode();
		stalinAstRoot.setPayload(payload);
		node.getPTestFile().apply(this);
		stalinAstRoot.addOutgoingNode(subtree);
	}
	
	
	@Override
	public void caseATestFile(ATestFile node) {
		IAnnotations annotations = new TestFile();
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		Payload payload = new Payload(null,"TestFile");		
		map.put(parser.getName(), annotations);
		payload.setAnnotations(map);
		AutomataASTNode testFile = new AutomataASTNode();
		testFile.setPayload(payload);
		for(PTestCase testCase : node.getTestCase()){
			testCase.apply(this);
			testFile.addOutgoingNode(subtree);
		}
		for(PAutomatonDefinition automatonDefinition : node.getAutomatonDefinition()){
			automatonDefinition.apply(this);
			testFile.addOutgoingNode(subtree);
		}
		subtree = testFile;
	}
	
	
	@Override
	public void caseANestedWordTestCase(ANestedWordTestCase node) {
		String testOperation = node.getTestOperation().getText();
		IAnnotations annotations = 
			new NestedWordTestCase(testOperation);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null, testOperation);
		payload.setAnnotations(map);
		AutomataASTNode finiteWordTestCase = new AutomataASTNode();
		finiteWordTestCase.setPayload(payload);
		
		PExpression pAutomaton = node.getExpression();
		pAutomaton.apply(this);
		finiteWordTestCase.addOutgoingNode(subtree);
		
		PNestedWord pNestedWord = node.getNestedWord();
		pNestedWord.apply(this);
		finiteWordTestCase.addOutgoingNode(subtree);

		subtree = finiteWordTestCase;
	}


	@Override
	public void caseANestedLassoWordTestCase(ANestedLassoWordTestCase node) {
		String testOperation = node.getTestOperation().getText();
		IAnnotations annotations = 
			new NestedLassoWordTestCase(testOperation);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null, testOperation);
		payload.setAnnotations(map);
		AutomataASTNode lassoWordTestCase = new AutomataASTNode();
		lassoWordTestCase.setPayload(payload);
		
		PExpression pExpression = node.getExpression();
		pExpression.apply(this);
		lassoWordTestCase.addOutgoingNode(subtree);
		
		PNestedWord pStem = node.getStem();
		pStem.apply(this);
		lassoWordTestCase.addOutgoingNode(subtree);
		
		PNestedWord pLoop = node.getLoop();
		pLoop.apply(this);
		lassoWordTestCase.addOutgoingNode(subtree);

		subtree = lassoWordTestCase;
	}


	@Override
	public void caseANoWordTestCase(ANoWordTestCase node) {
		String testOperation = node.getTestOperation().getText();
		IAnnotations annotations = 
			new NoWordTestCase(testOperation);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,testOperation);
		payload.setAnnotations(map);
		
		AutomataASTNode noWordTestCase = new AutomataASTNode();
		noWordTestCase.setPayload(payload);
		
		PExpression pAutomaton = node.getExpression();
		pAutomaton.apply(this);
		noWordTestCase.addOutgoingNode(subtree);
		
		subtree = noWordTestCase;
	}
	
	
	
	@Override
	public void caseAAutomatonNameExpression(AAutomatonNameExpression node) {
		String name = node.getName().getText();
		IAnnotations annotations = 
			new AutomatonNameExpression(name);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null, name);
		payload.setAnnotations(map);
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}

	@Override
	public void caseAOperationExpression(AOperationExpression node) {
		String operation = node.getOperation().getText();
		IAnnotations annotations = 
			new OperationExpression(operation);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,operation);
		payload.setAnnotations(map);
		AutomataASTNode automatonNameAutomatonNode = new AutomataASTNode();
		automatonNameAutomatonNode.setPayload(payload);
		
		for(PExpression pExpression : node.getExpressions()){
			pExpression.apply(this);
			automatonNameAutomatonNode.addOutgoingNode(subtree);
		}
		
		subtree = automatonNameAutomatonNode;
	}
	
	@Override
	public void caseANestedWord(ANestedWord node) {
		IAnnotations annotations = new NestedWord();
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"NestedWord");
		payload.setAnnotations(map);
		AutomataASTNode automatanode = new AutomataASTNode();
	
		for(Node symbol : node.getNestedWord()){
			symbol.apply(this);
			automatanode.addOutgoingNode(subtree);
		}
		subtree = automatanode;
		subtree.setPayload(payload);
	}
	
	@Override
	public void caseACallTaggedSymbol(ACallTaggedSymbol node){
		IAnnotations annotations = 
				new SymbolAtCallPosition(	node.getSymbol().getText());
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,node.getSymbol().getText()+"<");
		payload.setAnnotations(map);
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}
	
	@Override
	public void caseAInternalTaggedSymbol(AInternalTaggedSymbol node){
		IAnnotations annotations = 
				new SymbolAtInternalPosition(	node.getSymbol().getText());
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,node.getSymbol().getText());
		payload.setAnnotations(map);
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}
	
	@Override
	public void caseAReturnTaggedSymbol(AReturnTaggedSymbol node){
		IAnnotations annotations = 
				new SymbolAtReturnPosition(node.getSymbol().getText());
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,">"+node.getSymbol().getText());
		payload.setAnnotations(map);
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}
	
	
	@Override
	public void caseANwaAutomatonDefinition(ANwaAutomatonDefinition node){
		
		String name = node.getName().getText();
		ArrayList<String> callAlphabet = getArrayList(node.getCallAlphabet());	
		ArrayList<String> internalAlphabet = getArrayList(node.getInternalAlphabet());
		ArrayList<String> returnAlphabet = getArrayList(node.getReturnAlphabet());
		ArrayList<String> states  = getArrayList(node.getStates());
		ArrayList<String> initialStates = getArrayList(node.getInitialStates());
		ArrayList<String> finalStates = getArrayList(node.getFinalStates());
		
		IAnnotations annotations = new NwaDefinition(
				name,
				callAlphabet,
				internalAlphabet,
				returnAlphabet,
				states,
				initialStates,
				finalStates);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"Definition of NWA " + name);
		payload.setAnnotations(map);
		AutomataASTNode automatanode = new AutomataASTNode();
		
		for(PCallTransition call : node.getCallTransitions()){
			call.apply(this);
			automatanode.addOutgoingNode(subtree);
		}
		
		for(PInternalTransition internal : node.getInternalTransitions()){
			internal.apply(this);
			automatanode.addOutgoingNode(subtree);
		}
		
		for(PReturnTransition returnT : node.getReturnTransitions()){
			returnT .apply(this);
			automatanode.addOutgoingNode(subtree);
		}
		
		subtree = automatanode;
		subtree.setPayload(payload);
	}
	
	
	
	
	
	
	@Override
	public void caseACallTransition(ACallTransition node){
		IAnnotations annotations = new CallTransition(
				node.getPredecessor().getText(),
				node.getSymbol().getText(),
				node.getSuccessor().getText());
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"CallTransition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}
	
	@Override
	public void caseAInternalTransition(AInternalTransition node){
		IAnnotations annotations = new InternalTransition(
				node.getPredecessor().getText(),
				node.getSymbol().getText(),
				node.getSuccessor().getText());
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"InternalTransition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}
	
	@Override
	public void caseAReturnTransition(AReturnTransition node){
		IAnnotations annotations = new ReturnTransition(
				node.getPredecessor().getText(),
				node.getLinearPredecessor().getText(),
				node.getSymbol().getText(),
				node.getSuccessor().getText());
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"ReturnTransition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}
	

	@Override
	public void caseANetjulianAutomatonDefinition(ANetjulianAutomatonDefinition node) {
		String name = node.getName().getText();
		ArrayList<String> alphabet = getArrayList(node.getAlphabet());
		ArrayList<String> places  = getArrayList(node.getPlaces());
		ArrayList<String> initialMarking = getArrayList(((AMarking)node.getInitialMarking()).getPlaces());
		ArrayList<String> acceptingPlaces = getArrayList(node.getAcceptingPlaces());
		
		IAnnotations annotations = new PetriNetJulianDefinition(
				name,
				alphabet,
				places,
				initialMarking,
				acceptingPlaces);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"Definition of Petri Net " + name);
		payload.setAnnotations(map);
		AutomataASTNode automatanode = new AutomataASTNode();
		
		for(PNetTransition call : node.getTransitions()){
			call.apply(this);
			automatanode.addOutgoingNode(subtree);
		}
		
		subtree = automatanode;
		subtree.setPayload(payload);
	}

	@Override
	public void caseANetjanAutomatonDefinition(ANetjanAutomatonDefinition node){ 
		
		String name = node.getName().getText();
		ArrayList<String> alphabet = getArrayList(node.getAlphabet());
		ArrayList<String> places  = getArrayList(node.getPlaces());
		ArrayList<String> initialMarking = getArrayList(((AMarking)node.getInitialMarking()).getPlaces());
		
		ArrayList<ArrayList<String>> acceptingMarkings = new ArrayList<ArrayList<String>>();
		for(PMarking marking : node.getAcceptingMarkings())
			acceptingMarkings.add(getArrayList(((AMarking)marking).getPlaces()));
		
		IAnnotations annotations = new PetriNetJanDefinition(
				name,
				alphabet,
				places,
				initialMarking,
				acceptingMarkings);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"Definition of Petri Net " + name);
		payload.setAnnotations(map);
		AutomataASTNode automatanode = new AutomataASTNode();
		
		for(PNetTransition call : node.getTransitions()){
			call.apply(this);
			automatanode.addOutgoingNode(subtree);
		}
		
		subtree = automatanode;
		subtree.setPayload(payload);
	}

	@Override
    public void caseANetTransition(ANetTransition node){
		IAnnotations annotations = new TransitionDefinition(
				getArrayList(node.getPredecessors()),
				node.getSymbol().getText(),
				getArrayList(node.getSuccessors()));
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"Transition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode();
		subtree.setPayload(payload);
	}
}