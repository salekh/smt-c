#pragma once

#include "../solver/Manager.h"

#include "../modules/SimplexModule/SimplexModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class SimplexStrategy: public Manager
	{
		public:
			SimplexStrategy(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<SimplexModule<SimplexSettings1>>()
					})
				});
			}
	};
}	// namespace smtrat
