from DESops.automata.event.event import Event


def inserted_event(event):
    """
    Creates a new event matching the given label with the
        insered=True
        deleted=False
    Accepts either str (label) or Event as inputs
    """
    if isinstance(event, Event):
        label = event.label
    else:
        label = event
    d = {"inserted": True, "deleted": False}
    return Event(label, d)


def deleted_event(event):
    """
    Creates a new event matching the given label with the
        insered=False
        deleted=True
    Accepts either str (label) or Event as inputs
    """
    if isinstance(event, Event):
        label = event.label
    else:
        label = event
    d = {"inserted": False, "deleted": True}
    return Event(label, d)
