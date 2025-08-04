mtype = { credit,debit,wallet,insurance,none,success,failure,card_invalid,card_expired,generated,viewed,downloaded,printed }

// Global state variables for safety properties
bool client_1_initiated_booking = false;
bool client_2_initiated_booking = false;
bool unique_slot_booked_by_client_1 = false;
bool unique_slot_booked_by_client_2 = false;
bool unique_slot_is_available = true;
bool client_1_completed_payment = false;
bool client_1_present_for_service = false;
bool client_1_finished_booking = false;
bool client_1_cancelled_booking = false;

// LTL Safety Properties
ltl payment_before_service {
	[] (client_1_present_for_service -> client_1_completed_payment)
}

ltl no_double_booking {
	[] ((unique_slot_booked_by_client_1 -> !unique_slot_booked_by_client_2) && 
	(unique_slot_booked_by_client_2 -> !unique_slot_booked_by_client_1))
}

// LTL Liveness Properties
ltl booking_completion {
	[] (client_1_initiated_booking -> <> client_1_finished_booking)
}

ltl slot_availability_after_cancellation {
	[] (client_1_cancelled_booking -> <> unique_slot_is_available)
}

// Data structures
typedef CardInfo {
	int card_number;
	int expiry;
	int cvv;
	bool validated;
}

typedef WalletAuth {
	mtype provider;
	bool authenticated;
	int token;
}

typedef Invoice {
	int invoice_id;
	mtype status;
	mtype payment_method;
	int timestamp;
}

typedef FinancialRecord {
	mtype transaction_type;
	int amount;
	int timestamp;
	bool is_success
}

// Global channels
chan payment_request = [0] of { mtype };
chan invoice_channel = [0] of { mtype };
chan finance_log = [5] of { mtype };

// Helper functions
inline check_insurance_eligibility(user_id) {
	bool eligible = false;
	if
	:: user_id > 0 -> 
		eligible = true;
		printf("Insurance eligibility verified for user %d\n",user_id);
	:: else -> 
		eligible = false;
		printf("User %d not eligible for insurance\n",user_id);
	fi;
	return eligible;
}

inline validate_wallet(provider) {
	bool auth_success = false;
	if
	:: provider != none -> 
		auth_success = true;
		printf("Wallet authentication successful\n");
	:: else -> 
		auth_success = false;
		printf("Wallet authentication failed\n");
	fi;
	return auth_success;
}

// Tracks subscription status
bool recurring_active = false;

proctype Client() {
	mtype method;
	
// Initiate booking
	if
	:: true -> 
		client_1_initiated_booking = true;
		printf("Client 1 initiated booking\n");
		if
		:: unique_slot_is_available -> 
			unique_slot_booked_by_client_1 = true;
			unique_slot_is_available = false;
		:: else -> 
			printf("No slots available\n");
			goto end;
		fi;
	:: true -> 
		client_2_initiated_booking = true;
		printf("Client 2 initiated booking\n");
		if
		:: unique_slot_is_available -> 
			unique_slot_booked_by_client_2 = true;
			unique_slot_is_available = false;
		:: else -> 
			printf("No slots available\n");
			goto end;
		fi;
	fi;
	
// Continue with payment if booking successful
	if
	:: (unique_slot_booked_by_client_1 || unique_slot_booked_by_client_2) -> 
		// Client chooses a payment method
		if
		:: method = credit -> skip
		:: method = debit -> skip
		:: method = wallet -> skip
		:: method = insurance -> skip
		fi;
		
		printf("Client chose payment method: %e\n", method);
		payment_request!method;
	:: else -> 
		goto end;
	fi;
	
end:	// Add end label here
	skip;
	
// Client chooses a payment method
	if
	:: method = credit -> skip
	:: method = debit -> skip
	:: method = wallet -> skip
	:: method = insurance -> skip
	fi;
	
	printf("Client chose payment method: %e\n",method);
	payment_request!method;
}

proctype PaymentProcessor() {
	mtype method;
	bool validated = false;
	payment_request?method;
	printf("PaymentProcessor received payment using: %e\n",method);
	
// Validate payment method
	if
	:: method == insurance -> 
		validated = check_insurance_eligibility(_pid)
	:: method == wallet -> 
		validated = validate_wallet(method)
	:: else -> // credit or debit
		validated = true
	fi;
	
// Process payment if validated
	if
	:: validated -> 
		printf("Payment succeeded\n");
		client_1_completed_payment = true;
		invoice_channel!method;
		finance_log!method;
		recurring_active = true;
		client_1_finished_booking = true;
	:: else -> 
		printf("Payment failed - validation error\n");
		client_1_completed_payment = false;
		finance_log!none;
	fi;
}

proctype InvoiceSystem() {
	mtype method;
	Invoice current_invoice;
	
	do
	:: invoice_channel?method -> 
		current_invoice.invoice_id = _pid;
		current_invoice.payment_method = method;
		current_invoice.status = generated;
		printf("Invoice %d generated for payment method: %e\n",current_invoice.invoice_id,method);
		
// Simulate user actions
		if
		:: printf("Invoice %d viewed\n",current_invoice.invoice_id);
			current_invoice.status = viewed;
		:: printf("Invoice %d downloaded\n",current_invoice.invoice_id);
			current_invoice.status = downloaded;
		:: printf("Invoice %d printed\n",current_invoice.invoice_id);
			current_invoice.status = printed;
		fi;
	od
}

proctype RecurringBilling() {
	do
	:: (recurring_active) -> 
		printf("Recurring payment initiated\n");
// Send payment again
		payment_request!credit;
		break
	od
}

proctype FinanceReport() {
	mtype log_entry;
	FinancialRecord records[5];
	int record_count = 0;
	
	do
	:: finance_log?log_entry -> 
		if
		:: log_entry != none -> 
			records[record_count].transaction_type = log_entry;
			records[record_count].is_success = true;
			records[record_count].timestamp = _pid;
			record_count++;
			printf("Financial record added: %e\n",log_entry);
			
// Generate report when buffer is full
			if
			:: record_count == 5 -> 
				printf("Generating financial report...\n");
				record_count = 0;
			:: else -> skip;
			fi;
		:: else -> 
			printf("Failed transaction logged\n");
		fi;
	od
}

proctype ServiceAccess() {
    do
    :: true ->
        client_1_present_for_service = true;
        if
        :: client_1_completed_payment ->
            printf("Service access granted - payment verified\n");
        :: else ->
            printf("Service access denied - payment required\n");
        fi;
        
        // Handle cancellation
        if
        :: true ->
            client_1_cancelled_booking = true;
            unique_slot_booked_by_client_1 = false;
            unique_slot_is_available = true;
            printf("Booking cancelled\n");
        :: else -> skip;
        fi;
        break;
    od;
}init {
	atomic {
		run Client();
		run PaymentProcessor();
		run InvoiceSystem();
		run RecurringBilling();
		run FinanceReport();
		run ServiceAccess()
	}
}
