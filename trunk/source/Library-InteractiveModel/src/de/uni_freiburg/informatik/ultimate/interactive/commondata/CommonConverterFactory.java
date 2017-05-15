package de.uni_freiburg.informatik.ultimate.interactive.commondata;

import de.uni_freiburg.informatik.ultimate.interactive.conversion.IConverterFactory;

/**
 * marker interface for the Common-Interactive Plugin that registers its protobuf converter.
 * @author Julian Jarecki
 *
 * @param <S>
 */
public interface CommonConverterFactory<S> extends IConverterFactory<S,Object> {
}
