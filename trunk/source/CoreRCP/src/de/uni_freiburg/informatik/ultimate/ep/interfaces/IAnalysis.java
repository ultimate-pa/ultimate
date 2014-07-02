package de.uni_freiburg.informatik.ultimate.ep.interfaces;

/**
 * An interface all analysis plugins should implement.
 * 
 * An analysis tool is a tool that does not generate a new model, but instead
 * annotates or transforms an existing one.
 * 
 * As it is costly to enforce the structure of a model against a plugins' will,
 * Ultimate does not check whether an analysis plugin transforms the given mdoel
 * or not, it just assumes it does. Therefore, IAnalysis has to implement
 * {@link IModifyingTool}, although it may in fact not modify the model beyond
 * annotations, or not at all.
 * 
 * @author dietsch
 */
public interface IAnalysis extends IModifyingTool {

}
