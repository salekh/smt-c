#pragma once

#include <vector>
#include <boost/variant.hpp>

#include "../Common.h"

#include "TheoryTypes.h"

namespace smtrat {
namespace parser {
namespace conversion {

template<typename To>
struct Converter {
	template<typename From>
	bool operator()(const From&, To&) const {
		return false;
	}
	bool operator()(const To& from, To& to) const {
		to = from;
		return true;
	}
};

template<>
struct Converter<types::BVTerm> {
	template<typename From>
	bool operator()(const From&, types::BVTerm&) const {
		return false;
	}
	bool operator()(const types::BVTerm& from, types::BVTerm& to) const {
		to = from;
		return true;
	}
	bool operator()(const FixedWidthConstant<Integer>& from, types::BVTerm& to) const {
		carl::BVValue value(from.width);
		Integer v = from.value;
		
		assert(v >= 0);
		for (std::size_t i = 0; v > 0; i++) {
			if (carl::mod(v, 2) == 1) {
				value[i] = true;
				v = carl::div(v-1, Integer(2));
			} else {
				v = carl::div(v, Integer(2));
			}
		}
		to = types::BVTerm(carl::BVTermType::CONSTANT, value);
		return true;
	}
};

/**
 * Converts variants to some type using the Converter class.
 */
template<typename Res>
struct VariantConverter: public boost::static_visitor<> {
	typedef bool result_type;
	Res result;
	Converter<Res> converter;
	template<typename T>
	bool operator()(const T& t) {
		return converter(t, result);
	}
	template<typename... T>
	bool operator()(const boost::variant<T...>& t) {
		return boost::apply_visitor(*this, t);
	}
	template<typename... T>
	bool operator()(const boost::variant<T...>& t, Res& r) {
		if ((*this)(t)) {
			r = result;
			return true;
		}
		return false;
	}
	template<typename T>
	Res convert(const T& t) {
		if ((*this)(t)) return result;
		else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to convert \"" << t << "\" to " << typeid(T).name() << ".");
			return Res();
		}
	}
};

/**
 * Converts variants to another variant type not using the Converter class.
 */
template<typename Res>
struct VariantVariantConverter: public boost::static_visitor<> {
	typedef Res result_type;
	template<typename T>
	Res operator()(const T& t) {
		return Res(t);
	}
	template<typename... T>
	Res convert(const boost::variant<T...>& t) {
		return boost::apply_visitor(*this, t);
	}
};


/**
 * Converts a vector of variants to a vector of some type using the Converter class.
 */
template<typename Res>
struct VectorVariantConverter: public boost::static_visitor<> {
	typedef Res result_type;
	template<typename... T>
	bool operator()(const std::vector<boost::variant<T...>>& v, std::vector<Res>& result) const {
		result.clear();
		VariantConverter<Res> vc;
		for (const auto& val: v) {
			if (vc(val)) result.push_back(vc.result);
			else return false;
		}
		return true;
	}
	template<typename... T>
	bool operator()(const std::vector<boost::variant<T...>>& v, std::vector<Res>& result, TheoryError& errors) const {
		result.clear();
		VariantConverter<Res> vc;
		for (const auto& val: v) {
			if (vc(val)) result.push_back(vc.result);
			else {
				errors.next() << "Failed to convert \"" << val << "\" to " << typeid(Res).name() << ".";
				return false;
			}
		}
		return true;
	}
};

}
}
}
