package de.uni_freiburg.informatik.ultimate.automata.parser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PushbackReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.analysis.DepthFirstAdapter;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.lexer.Lexer;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.lexer.LexerException;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AAutomatonNameExpression;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ACallTaggedSymbol;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ACallTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AInternalTaggedSymbol;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AMarking;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANestedLassoWordTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANestedWord;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANestedWordTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANetTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANetjanAutomatonDefinition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANetjulianAutomatonDefinition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANoWordTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ANwaAutomatonDefinition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AOperationExpression;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AQuotedIdentifier;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AReturnTaggedSymbol;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.ATestFile;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.AUnquotedIdentifier;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.Node;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PAutomatonDefinition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PExpression;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PIdentifier;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PMarking;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PNestedWord;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PNetTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.PTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.node.Start;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.parser.Parser;
import de.uni_freiburg.informatik.ultimate.automata.parser.TestGrammar.parser.ParserException;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.AutomatonNameExpression;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.NestedLassoWordTestCase;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.NestedWord;
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
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.Payload;

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
	private INode ultimateAstRoot, subtree;

	/**
	 * when parsing a noch which has an identifier as a child, we descend 
	 * parsing into the child (the identifier) write what we parsed to
	 * lastIdentifier and access this when we return from decending to the
	 * child
	 */
	private String lastIdentifier;
	private AutomataParser parser;
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
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
		return ultimateAstRoot;
	}
	
	
	public ArrayList<String> getArrayList(LinkedList<PIdentifier> list) {
		ArrayList<String> al = new ArrayList<String>(list.size());
		for(PIdentifier pIdentifier : list){
			pIdentifier.apply(this);
			assert (lastIdentifier != null);
			String id = lastIdentifier;
			lastIdentifier = null;
			al.add(id);
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
		ultimateAstRoot = new AutomataASTNode(payload);
		node.getPTestFile().apply(this);
		ultimateAstRoot.addOutgoingNode(subtree);
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
		node.getName().apply(this);
		assert (lastIdentifier != null);
		String name = lastIdentifier;
		lastIdentifier = null;
		IAnnotations annotations = 
			new AutomatonNameExpression(name);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null, name);
		payload.setAnnotations(map);
		subtree = new AutomataASTNode(payload);
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
		subtree = new AutomataASTNode(payload);
	}
	
	@Override
	public void caseACallTaggedSymbol(ACallTaggedSymbol node){
		node.getSymbol().apply(this);
		assert (lastIdentifier != null);
		String letter = lastIdentifier;
		lastIdentifier = null;
		
		IAnnotations annotations = new SymbolAtCallPosition(letter);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,letter+"<");
		payload.setAnnotations(map);
		subtree = new AutomataASTNode(payload);
	}
	
	@Override
	public void caseAInternalTaggedSymbol(AInternalTaggedSymbol node){
		node.getSymbol().apply(this);
		assert (lastIdentifier != null);
		String letter = lastIdentifier;
		lastIdentifier = null;
		
		IAnnotations annotations = 
				new SymbolAtInternalPosition(letter);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,letter);
		payload.setAnnotations(map);
		subtree = new AutomataASTNode(payload);
	}
	
	@Override
	public void caseAReturnTaggedSymbol(AReturnTaggedSymbol node){
		node.getSymbol().apply(this);
		assert (lastIdentifier != null);
		String letter = lastIdentifier;
		lastIdentifier = null;
		
		IAnnotations annotations = new SymbolAtReturnPosition(letter);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,">"+letter);
		payload.setAnnotations(map);
		subtree = new AutomataASTNode(payload);
	}
	
	
	@Override
	public void caseANwaAutomatonDefinition(ANwaAutomatonDefinition node){
		
		node.getName().apply(this);
		assert (lastIdentifier != null);
		String name = lastIdentifier;
		lastIdentifier = null;
		
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
		AutomataASTNode automatanode = new AutomataASTNode(payload);
		
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
	}
	
	
	
	
	
	
	@Override
	public void caseACallTransition(ACallTransition node){
		node.getPredecessor().apply(this);
		assert (lastIdentifier != null);
		String precedessorId = lastIdentifier;
		lastIdentifier = null;
		
		node.getSymbol().apply(this);
		assert (lastIdentifier != null);
		String symbolId = lastIdentifier;
		lastIdentifier = null;
		
		node.getSuccessor().apply(this);
		assert (lastIdentifier != null);
		String successorId = lastIdentifier;
		lastIdentifier = null;




		
		IAnnotations annotations = new CallTransition(
				precedessorId,
				symbolId,
				successorId);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"CallTransition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode(payload);
	}
	
	@Override
	public void caseAInternalTransition(AInternalTransition node){
		node.getPredecessor().apply(this);
		assert (lastIdentifier != null);
		String precedessorId = lastIdentifier;
		lastIdentifier = null;
		
		node.getSymbol().apply(this);
		assert (lastIdentifier != null);
		String symbolId = lastIdentifier;
		lastIdentifier = null;
		
		node.getSuccessor().apply(this);
		assert (lastIdentifier != null);
		String successorId = lastIdentifier;
		lastIdentifier = null;
		
		IAnnotations annotations = new InternalTransition(
				precedessorId,
				symbolId,
				successorId);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"InternalTransition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode(payload);
	}
	
	@Override
	public void caseAReturnTransition(AReturnTransition node){
		node.getPredecessor().apply(this);
		assert (lastIdentifier != null);
		String precedessorId = lastIdentifier;
		lastIdentifier = null;
		
		node.getLinearPredecessor().apply(this);
		assert (lastIdentifier != null);
		String hierarchicalPredecessorId = lastIdentifier;
		lastIdentifier = null;
		
		node.getSymbol().apply(this);
		assert (lastIdentifier != null);
		String symbolId = lastIdentifier;
		lastIdentifier = null;
		
		node.getSuccessor().apply(this);
		assert (lastIdentifier != null);
		String successorId = lastIdentifier;
		lastIdentifier = null;
		
		IAnnotations annotations = new ReturnTransition(
				precedessorId,
				hierarchicalPredecessorId,
				symbolId,
				successorId);
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"ReturnTransition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode(payload);
	}
	

	@Override
	public void caseANetjulianAutomatonDefinition(ANetjulianAutomatonDefinition node) {
		
		node.getName().apply(this);
		assert (lastIdentifier != null);
		String name = lastIdentifier;
		lastIdentifier = null;
		
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
		
		subtree = new AutomataASTNode(payload);
	}

	@Override
	public void caseANetjanAutomatonDefinition(ANetjanAutomatonDefinition node){ 
		
		node.getName().apply(this);
		assert (lastIdentifier != null);
		String name = lastIdentifier;
		lastIdentifier = null;
		
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
		
		subtree = new AutomataASTNode(payload);
	}

	@Override
    public void caseANetTransition(ANetTransition node){
		
		node.getSymbol().apply(this);
		assert (lastIdentifier != null);
		String transitionName = lastIdentifier;
		lastIdentifier = null;
		
		IAnnotations annotations = new TransitionDefinition(
				getArrayList(node.getPredecessors()),
				transitionName,
				getArrayList(node.getSuccessors()));
		HashMap<String, IAnnotations> map = new HashMap<String, IAnnotations>();
		map.put(parser.getName(), annotations);
		Payload payload = new Payload(null,"Transition");
		payload.setAnnotations(map);
		
		subtree = new AutomataASTNode(payload);
	}
	
	@Override
    public void caseAUnquotedIdentifier(AUnquotedIdentifier node){
		lastIdentifier = node.getId().getText();
	}
	
	@Override
    public void caseAQuotedIdentifier(AQuotedIdentifier node){
		// remove quotes \" at the beginning and end of the identifier
		String quotedIdentifier = node.getId().getText();
		int length = quotedIdentifier.length();
		assert((quotedIdentifier.substring(0, 1)).equals("\""));
		assert((quotedIdentifier.substring(length-1, length)).equals("\""));
		lastIdentifier = quotedIdentifier.substring(1, length-1);
		assert(!lastIdentifier.equals(""));
	}
	
}