mtype = { credit, debit, wallet, insurance, none, success, failure, card_invalid, card_expired, generated, viewed, downloaded, printed }

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
        printf("Insurance eligibility verified for user %d\n", user_id);
    :: else -> 
        eligible = false;
        printf("User %d not eligible for insurance\n", user_id);
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

    // Client chooses a payment method
    if
    :: method = credit -> skip
    :: method = debit -> skip
    :: method = wallet -> skip
    :: method = insurance -> skip
    fi;

    printf("Client chose payment method: %e\n", method);
    payment_request!method;
}

proctype PaymentProcessor() {
    mtype method;
    bool validated = false;
    payment_request?method;
    printf("PaymentProcessor received payment using: %e\n", method);

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
        invoice_channel!method;
        finance_log!method;
        recurring_active = true;
    :: else ->
        printf("Payment failed - validation error\n");
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
        printf("Invoice %d generated for payment method: %e\n", current_invoice.invoice_id, method);
        
        // Simulate user actions
        if
        :: printf("Invoice %d viewed\n", current_invoice.invoice_id);
           current_invoice.status = viewed;
        :: printf("Invoice %d downloaded\n", current_invoice.invoice_id);
           current_invoice.status = downloaded;
        :: printf("Invoice %d printed\n", current_invoice.invoice_id);
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
            printf("Financial record added: %e\n", log_entry);
            
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

init {
    atomic {
        run Client();
        run PaymentProcessor();
        run InvoiceSystem();
        run RecurringBilling();
        run FinanceReport()
    }
}
