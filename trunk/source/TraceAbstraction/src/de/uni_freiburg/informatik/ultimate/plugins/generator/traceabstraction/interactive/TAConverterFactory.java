package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import de.uni_freiburg.informatik.ultimate.interactive.conversion.IConverterFactory;

/**
 * marker interface for the TA-Interactive Plugin that registers its protobuf converter.
 * @author Julian Jarecki
 *
 * @param <S>
 */
public interface TAConverterFactory<S> extends IConverterFactory<S,Object> {
}
