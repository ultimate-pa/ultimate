/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState.ArrayData;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState.CallStackElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * @author Christopher Dillo
 *
 */
public class StateChangeLogger implements IAbstractStateChangeListener {
	
	private boolean m_logToConsole;
	private boolean m_logToFile;
	
	private PrintWriter m_writer;
	
	private Logger m_logger;
	
	public StateChangeLogger(Logger logger, boolean logToConsole, boolean logToFile, String fileName) {
		m_logToConsole = logToConsole;
		m_logger = logger;
		m_logToFile = logToFile && (fileName != null);

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

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.IAbstractStateChangeListener#onStateChange(de.uni_freiburg.informatik.ultimate.model.IElement, java.util.List, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState)
	 */
	@Override
	public void onStateChange(RCFGEdge viaEdge, List<AbstractState> oldStates,
			AbstractState newState, AbstractState mergedState) {
		StringBuilder output = new StringBuilder();
		output.append("~~~ STATE CHANGE ~~~\n");
		
		output.append("From ");
		RCFGNode source = viaEdge.getSource();
		if (source instanceof ProgramPoint) {
			output.append(((ProgramPoint) source).getLocationName());
		} else {
			output.append(source.toString());
		}
		RCFGNode target = viaEdge.getTarget();
		String targetName;
		if (target instanceof ProgramPoint) {
			targetName = ((ProgramPoint) target).getLocationName();
		} else {
			targetName = target.toString();
		}
		output.append(String.format(" to %s via\n\n", targetName));
		if (viaEdge instanceof CodeBlock) {
			output.append(((CodeBlock) viaEdge).getPrettyPrintedStatements());
		} else {
			output.append(viaEdge.toString());
		}

		output.append("\n\nNew state:\n");
		logState(newState, targetName, output);

		if (mergedState != newState) {
			output.append("\n-> Merged/widened state:\n");
			logState(mergedState, targetName, output);
		}
		
		String stateInfo = output.toString();

		if (m_logToConsole) {
			m_logger.info(stateInfo);
		}
		
		if (m_logToFile) {
			m_writer.println(stateInfo);
			m_writer.flush();
		}
	}
	
	private void logState(AbstractState state, String targetName, StringBuilder output) {
		List<CallStackElement> callStack = state.getCallStack();
		for (CallStackElement cse : callStack) {
			CallStatement cs = cse.getCallStatement();
			output.append(String.format("\tCall stack level: %s\n", (cs == null) ? "GLOBAL" : cs.getMethodName()));
			Map<String, IAbstractValue<?>> values = cse.getValues();
			if (!values.isEmpty()) {
				output.append("\t\tValues:\n");
				for (String identifier : values.keySet()) {
					IAbstractValue<?> value = values.get(identifier);
					output.append(String.format("\t\t\t%s -> %s\n", identifier, value));
				}
			}
			Map<String, ArrayData> arrays = cse.getArrays();
			if (!arrays.isEmpty()) {
				output.append("\t\tArrays:\n");
				for (String identifier : arrays.keySet()) {
					ArrayData array = arrays.get(identifier);
					output.append(String.format("\t\t\t%s -> %s\n", identifier, array.getValue()));
					if (array.getIndicesUnclear())
						output.append("\t\t\t\tStoring to ambiguous indices has occured.\n");
				}
			}
		}
		output.append("\tTrace: Root");
		List<RCFGNode> trace = state.getPassedNodes();
		for (RCFGNode n : trace) {
			output.append(" -> ");
			if (n instanceof ProgramPoint) {
				output.append(((ProgramPoint) n).getLocationName());
			} else {
				output.append(n.toString());
			}
		}
		output.append(String.format(" -> %s\n", targetName));
	}

}
