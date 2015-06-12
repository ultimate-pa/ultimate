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
	private ArrayList<Pair<RCFGEdge, RCFGNode> > m_openLoops;
	
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
			m_preconditions = values;
		}
		public void setPostcondition(HashMap<AbstractState.Pair, Object> values) {
			m_postconditions = values;
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
			str += "Contract for function " + m_functionName + ": ";
			str += "Precondition = ";
			str += m_preconditions.toString();
			str += ", Postcondition = ";
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
	
				// Get variable values pointer
				if (CS.get(functionName)!=null) {
					LinkedHashMap<String, Object> values = (LinkedHashMap<String, Object>) CS.get(functionName);
					if (values.get("Values")!=null) {
						 VALS = (HashMap<AbstractState.Pair, Object>) values.get("Values");
					}
				}
			}
		}
		return VALS;
	}
	
	public CodeAnnotator(Logger logger, boolean logToConsole, boolean logToFile, String fileName) {
		m_logger = logger;
		m_logToFile = logToFile && (fileName != null);
		m_openLoops = new ArrayList<Pair<RCFGEdge, RCFGNode> >();

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
		// Create contract
		prePostContract contract = new prePostContract();
		contract.setFunctionName(functionName);

		// set precondition in contract
		contract.setPrecondition(getValuesInFunction(functionName, postconditionNode));
		
		// set postcondition in contract
		contract.setPostcondition(getValuesInFunction(functionName, preconditionNode));
		
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
	
	@Override
	public void onStateChange(RCFGEdge viaEdge, List<AbstractState> oldStates,
			AbstractState newState, AbstractState mergedState) {
		// Get source and target node of current state change
		RCFGNode source = viaEdge.getSource();		
		
		// Write a function contract if viaEdge is a return edge
		try{
			Return ret = (Return) viaEdge;		
			// Get call edge and function name
			Call call = ret.getCorrespondingCall();
			RCFGNode callTarget = call.getTarget();
			CallStatement cst = call.getCallStatement();
			String functionName = cst.getMethodName();			
			writeContractAnnotation(functionName, source, callTarget);
			return;
		}
		catch(ClassCastException e){}; // Current state change is no return edge
		
		// Write loop invariant if viaEdge terminates a loop TODO
		RCFGNode entryNode = (RCFGNode) newState.peekLoopEntry().getLoopNode();
		RCFGEdge exitEdge = newState.peekLoopEntry().getExitEdge();		
		if (entryNode == source) {
			m_openLoops.add(new Pair<RCFGEdge, RCFGNode>(exitEdge, entryNode));
			m_logger.error("Loop entry found: " + source + " (will be exited through " + exitEdge + ")");
		}
		else if (m_openLoops.size() > 0) {
			m_logger.warn("Open loops: " + m_openLoops);
			if(viaEdge == m_openLoops.get(m_openLoops.size() - 1).first) {
				m_openLoops.remove(m_openLoops.size() - 1);
				m_logger.error("Loop terminated with edge " + viaEdge);
			}
		}
	}
}