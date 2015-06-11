/* 
 * @file   ParserState.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../Common.h"
#include "TheoryTypes.h"
#include "FunctionInstantiator.h"

namespace smtrat {
namespace parser {
	
	struct InstructionHandler;
	
	struct ParserState {

		struct ExpressionScope {
		private:
			std::map<std::string, types::TermType> bindings;
		public:
			ExpressionScope(const ParserState& state)
			{
				this->bindings = state.bindings;
			}
			void discharge(ParserState& state) {
				state.bindings = std::move(this->bindings);
			}
		};
		
		struct ScriptScope {
		private:
			std::map<std::string, types::TermType> constants;
			std::map<std::string, types::VariableType> variables;
			std::map<std::string, carl::UninterpretedFunction> declared_functions;
			std::map<std::string, const FunctionInstantiator*> defined_functions;
			std::map<std::string, const IndexedFunctionInstantiator*> defined_indexed_functions;
			std::map<std::string, const UserFunctionInstantiator*> defined_user_functions;
		public:
			ScriptScope(const ParserState& state)
			{
				this->constants = state.constants;
				this->variables = state.variables;
				this->declared_functions = state.declared_functions;
				this->defined_functions = state.defined_functions;
				this->defined_indexed_functions = state.defined_indexed_functions;
				this->defined_user_functions = state.defined_user_functions;
			}
			void discharge(ParserState& state) {
				state.constants = std::move(this->constants);
				state.variables = std::move(this->variables);
				state.declared_functions = std::move(this->declared_functions);
				state.defined_functions = std::move(this->defined_functions);
				state.defined_indexed_functions = std::move(this->defined_indexed_functions);
				state.defined_user_functions = std::move(this->defined_user_functions);
			}
		};
		
		std::set<types::VariableType> auxiliary_variables;
		std::map<std::string, types::TermType> bindings;
		std::map<std::string, types::TermType> constants;
		std::map<std::string, types::VariableType> variables;
		std::map<std::string, carl::UninterpretedFunction> declared_functions;
		std::map<std::string, const FunctionInstantiator*> defined_functions;
		std::map<std::string, const IndexedFunctionInstantiator*> defined_indexed_functions;
		std::map<std::string, const UserFunctionInstantiator*> defined_user_functions;
		FormulasT global_formulas;
		
		InstructionHandler* handler;
		
		std::stack<ExpressionScope> expressionScopes;
		std::stack<ScriptScope> scriptScopes;
		
		ParserState(InstructionHandler* ih): handler(ih) {
		}
		~ParserState() {
			while (!scriptScopes.empty()) popScriptScope();
			for (auto& it: defined_functions) delete it.second;
			for (auto& it: defined_indexed_functions) delete it.second;
			for (auto& it: defined_user_functions) delete it.second;
			defined_functions.clear();
			defined_indexed_functions.clear();
			defined_user_functions.clear();
		}
		
		void pushExpressionScope() {
			expressionScopes.emplace(*this);
		}
		void popExpressionScope() {
			expressionScopes.top().discharge(*this);
			expressionScopes.pop();
		}
		void pushScriptScope() {
			assert(expressionScopes.empty());
			scriptScopes.emplace(*this);
		}
		void popScriptScope() {
			assert(expressionScopes.empty());
			scriptScopes.top().discharge(*this);
			scriptScopes.pop();
		}

		
		void errorMessage(const std::string& msg) {
			std::cerr << "Parser error: " << msg << std::endl;
		}
		bool isSymbolFree(const std::string& name, bool output = true) {
				std::stringstream out;
				if (name == "true" || name == "false") out << "\"" << name << "\" is a reserved keyword.";
				else if (variables.find(name) != variables.end()) out << "\"" << name << "\" has already been defined as a variable.";
				else if (bindings.find(name) != bindings.end()) out << "\"" << name << "\" has already been defined as a binding to \"" << bindings[name] << "\".";
				else if (constants.find(name) != constants.end()) out << "\"" << name << "\" has already been defined as a constant.";
				else if (declared_functions.find(name) != declared_functions.end()) out << "\"" << name << "\" has already been declared as a function.";
				else if (defined_functions.find(name) != defined_functions.end()) out << "\"" << name << "\" has already been defined as a function.";
				else if (defined_indexed_functions.find(name) != defined_indexed_functions.end()) out << "\"" << name << "\" has already been defined as a function.";
				else if (defined_user_functions.find(name) != defined_user_functions.end()) out << "\"" << name << "\" has already been defined as a function by the user.";
				else return true;
				if (output) SMTRAT_LOG_ERROR("smtrat.parser", out.str());
				return false;
		}
		
		template<typename Res, typename T>
		bool resolveSymbol(const std::string& name, const std::map<std::string, T>& map, Res& result) const {
			auto it = map.find(name);
			if (it == map.end()) return false;
			result = it->second;
			return true;
		}
		
		bool resolveSymbol(const std::string& name, types::TermType& r) const {
			if (resolveSymbol(name, variables, r)) return true;
			if (resolveSymbol(name, bindings, r)) return true;
			if (resolveSymbol(name, constants, r)) return true;
			return false;
		}
		
		void registerFunction(const std::string& name, const FunctionInstantiator* fi) {
			if (!isSymbolFree(name)) {
				SMTRAT_LOG_ERROR("smtrat.parser", "Failed to register function \"" << name << "\", name is already used.");
				return;
			}
			defined_functions.emplace(name, fi);
		}
		void registerFunction(const std::string& name, const IndexedFunctionInstantiator* fi) {
			if (!isSymbolFree(name)) {
				SMTRAT_LOG_ERROR("smtrat.parser", "Failed to register indexed function \"" << name << "\", name is already used.");
				return;
			}
			defined_indexed_functions.emplace(name, fi);
		}
		void registerFunction(const std::string& name, const UserFunctionInstantiator* fi) {
			if (!isSymbolFree(name)) {
				SMTRAT_LOG_ERROR("smtrat.parser", "Failed to register user function \"" << name << "\", name is already used.");
				return;
			}
			defined_user_functions.emplace(name, fi);
		}
	};

}
}
