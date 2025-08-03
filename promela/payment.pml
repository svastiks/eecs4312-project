mtype = { credit, debit, wallet, insurance, none, success, failure }

// Global channels
chan payment_request = [0] of { mtype };
chan invoice_channel = [0] of { mtype };
chan finance_log = [5] of { mtype };

// Tracks subscription status
bool recurring_active = false;

proctype Client() {
    mtype method;

    // Client chooses a payment method
    if
    :: method = credit
    :: method = debit
    :: method = wallet
    :: method = insurance
    fi;

    printf("Client chose payment method: %e\n", method);
    payment_request!method;
}

proctype PaymentProcessor() {
    mtype method;
    payment_request?method;
    printf("PaymentProcessor received payment using: %e\n", method);

    // Simulate success/failure
    if
    :: printf("Payment succeeded\n");
       invoice_channel!method;
       finance_log!method;
       recurring_active = true;
    :: printf("Payment failed\n");
       finance_log!none;
    fi;
}

proctype InvoiceSystem() {
    mtype method;
    invoice_channel?method;
    printf("Invoice generated for payment method: %e\n", method);
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
    do
    :: finance_log?log_entry ->
        if
        :: log_entry != none ->
            printf("Finance log updated for: %e\n", log_entry)
        :: else ->
            printf("Finance log error: payment failed\n")
        fi
    od
}
