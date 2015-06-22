/**
 * @author Thomas Strump
 *
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class CodeAnnotator implements IAbstractStateChangeListener {
	
	private boolean m_logToFile;
	private PrintWriter m_writer;	
	private Logger m_logger;
	private ArrayList<Pair<HashMap<AbstractState.Pair, Object>, RCFGNode> > m_openLoops;
	
	public class Pair<f,s> {
		public Pair(f fi, s se){
			first = fi;
			second = se;
		}
		public f first;
		public s second;
		public String toString() {
			String ret = "First = " + first + ", Second = " + second;
			return ret;
		}
	}
	
	public class prePostContract{
		public prePostContract(){
			m_preconditions = new HashMap<AbstractState.Pair, Object>();
			m_postconditions = new HashMap<AbstractState.Pair, Object>();
		}
		public void setPrecondition(HashMap<AbstractState.Pair, Object> values) {
			m_preconditions = new HashMap<AbstractState.Pair, Object>(values);
		}
		public void setPostcondition(HashMap<AbstractState.Pair, Object> values) {
			m_postconditions = new HashMap<AbstractState.Pair, Object>(values);
		}
		public HashMap<AbstractState.Pair, Object> getPrecondition() {
			return m_preconditions;
		}
		public HashMap<AbstractState.Pair, Object> getPostcondition() {
			return m_postconditions;
		}
		public void setFunctionName(String name) {
			m_functionName = name;
		}
		public boolean isValid() {
			return !(m_preconditions == null && m_postconditions == null);
		}
		public String toString(){
			String str = new String();
			str += "Contract for function " + m_functionName + ": \n";
			str += "Precondition = ";
			str += m_preconditions.toString();
			str += ", \nPostcondition = ";
			str += m_postconditions.toString();
			return str;
		}	
		private HashMap<AbstractState.Pair, Object> m_preconditions;
		private HashMap<AbstractState.Pair, Object> m_postconditions;
		private String m_functionName;
	
	}
	
	private HashMap<AbstractState.Pair, Object> getValuesInFunction(String functionName, RCFGNode node) {
		HashMap<AbstractState.Pair, Object> VALS = new HashMap<AbstractState.Pair, Object>(); 
		AbstractInterpretationAnnotations annot = AbstractInterpretationAnnotations.getAnnotation(node);
		ArrayList<Object> AbsStates = (ArrayList<Object>) annot.getFieldValue("Abstract states");
		
		if (AbsStates != null) {
			java.util.Iterator<Object> it = AbsStates.iterator();
			while (it.hasNext()) { 			
				//TODO: More than one abstract state possible?
				// If so, which abstract states of ENTRY node belongs to which abstract state of EXIT node?	
				LinkedHashMap<String, Object> HM = (LinkedHashMap<String, Object>) it.next();
				LinkedHashMap<String, Object> CS = (LinkedHashMap<String, Object>) HM.get("Call stack");
	
				// Variable values of current function
				if (CS.get(functionName)!=null) {
					LinkedHashMap<String, Object> values = (LinkedHashMap<String, Object>) CS.get(functionName);
					if (values.get("Values")!=null) {
						 VALS = (HashMap<AbstractState.Pair, Object>) values.get("Values");
					}
				}
				
				// Global variable values
				if (CS.get("GLOBAL")!=null) {
					LinkedHashMap<String, Object> global = (LinkedHashMap<String, Object>) CS.get("GLOBAL");
					if (global.get("Values")!=null) {
						HashMap<AbstractState.Pair, Object> globalValues = (HashMap<AbstractState.Pair, Object>) global.get("Values");
						VALS.putAll(globalValues);
					}
				}			
			}
		}
		return VALS;
	}
		
	public CodeAnnotator(Logger logger, boolean logToConsole, boolean logToFile, String fileName) {
		m_logger = logger;
		m_logToFile = logToFile && (fileName != null);
		m_openLoops = new ArrayList<Pair<HashMap<AbstractState.Pair, Object>, RCFGNode> >();

		m_writer = null;
		if (m_logToFile) {
			// open file to write to
			try {
				File file = new File(fileName);
				if (file.isFile() && file.canWrite() || !file.exists()) {
					if (file.exists()) {
						m_logger.info(String.format("File \"%s\" already exists and will be overwritten.",
								file.getAbsolutePath()));
					}
					file.createNewFile();
					m_logger.info(String.format("Logging state changes to \"%s\"",
							file.getAbsolutePath()));
					m_writer = new PrintWriter(new FileWriter(file));
				} else {
					m_logger.warn(String.format("Can't write to file \"%s\"",
							file.getAbsolutePath()));
					file = null;
				}
			} catch (IOException e) {
				m_logger.error(String.format("Can't open file \"%s\"", fileName), e);
			}
			m_logToFile = (m_writer != null);
		}
	}
	
	private void writeContractAnnotation(String functionName, RCFGNode preconditionNode, RCFGNode postconditionNode){
		m_logger.debug("Writing contract annotation for function " + functionName);
		// Create contract
		prePostContract contract = new prePostContract();
		contract.setFunctionName(functionName);

		// set precondition in contract
		contract.setPrecondition(getValuesInFunction(functionName, preconditionNode));
		
		// set postcondition in contract
		contract.setPostcondition(getValuesInFunction(functionName, postconditionNode));
		
		// Add contract annotation to node payload
		if (contract.isValid()) {
			// Get or create "Contract Annotations" payload for function call node
			HashMap<String, IAnnotations> annotMap = postconditionNode.getPayload().getAnnotations();
			DefaultAnnotations contractAnnot = (DefaultAnnotations) annotMap.get("Contract Annotations");
			if (annotMap.get("Contract Annotations") == null) {
				contractAnnot = new DefaultAnnotations();
				annotMap.put("Contract Annotations", contractAnnot);
			}
			// Write contract to the first unused slot in "Contract Annotations" payload of function call node
			Integer entryNum = new Integer(0);
			while(true) {
				if (contractAnnot.get(entryNum.toString()) == null) {
					contractAnnot.put(entryNum.toString(), contract);
					break;
				}
				entryNum++;
			}		
		}
	}
	
	private void writeLoopAnnotation(HashMap<AbstractState.Pair, Object> precondition, RCFGNode postconditionNode, String scope){
		m_logger.debug("Writing loop annotation for scope " + scope);
		
		// Create contract
		prePostContract contract = new prePostContract();
		contract.setFunctionName("loop");

		// set precondition in contract
		contract.setPrecondition(precondition);
		
		// set postcondition in contract
		contract.setPostcondition(getValuesInFunction(scope, postconditionNode));
		
		// Add contract annotation to node payload
		if (contract.isValid()) {
			// Get or create "Contract Annotations" payload for function call node
			HashMap<String, IAnnotations> annotMap = postconditionNode.getPayload().getAnnotations();
			DefaultAnnotations contractAnnot = (DefaultAnnotations) annotMap.get("Contract Annotations");
			if (annotMap.get("Contract Annotations") == null) {
				contractAnnot = new DefaultAnnotations();
				annotMap.put("Contract Annotations", contractAnnot);
			}
			// Write contract to the first unused slot in "Contract Annotations" payload of function call node
			Integer entryNum = new Integer(0);
			while(true) {
				if (contractAnnot.get(entryNum.toString()) == null) {
					contractAnnot.put(entryNum.toString(), contract);
					m_logger.warn( contract.toString());
					break;
				}
				entryNum++;
			}		
		}
	}
	
	@Override
	public void onStateChange(RCFGEdge viaEdge, List<AbstractState> oldStates,
			AbstractState newState, AbstractState mergedState) {
		
		// Get source and target node of current state change
		RCFGNode source = viaEdge.getSource();		
		
		// Write a function contract if viaEdge is a return edge
		if (viaEdge instanceof Return) {
			Return ret = (Return) viaEdge;
			// Get call edge and function name
			m_logger.debug("Writing function contract for return edge: " + ret);
			Call call = ret.getCorrespondingCall();
			RCFGNode callTarget = call.getTarget();
			CallStatement cst = call.getCallStatement();
			String functionName = cst.getMethodName();
			writeContractAnnotation(functionName, callTarget, source);
			return;
		}
		
		// Write loop invariant if viaEdge terminates a loop
		RCFGNode target = viaEdge.getTarget();
		String scope = newState.getCurrentScopeName();
		m_logger.debug("Current scope : " + scope);
		
		// Check for the start of a loop
		if (source == newState.peekLoopEntry().getLoopNode()) {
			m_logger.debug("Contract Annotator: loop started at node: " + source);
			HashMap<AbstractState.Pair, Object> sourceValues = getValuesInFunction(scope, source);
			Pair<HashMap<AbstractState.Pair, Object>, RCFGNode> pair 
					= new Pair<HashMap<AbstractState.Pair,Object>, RCFGNode>(sourceValues, source);
			m_openLoops.add(pair);
			m_logger.debug("Open loops after adding: " + m_openLoops);
		}
		// Check for the end of a loop
		else if (m_openLoops.size() > 0){
			if (target == m_openLoops.get(m_openLoops.size()-1).second) {
				m_logger.debug("Contract Annotator: loop closed at node: " + target);
				writeLoopAnnotation(m_openLoops.get(m_openLoops.size()-1).first, target, scope);
				m_openLoops.remove(m_openLoops.size()-1);
			}
		}
	}
}